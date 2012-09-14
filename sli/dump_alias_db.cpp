#include <sys/types.h>
#include <sys/fcntl.h>
#include <sys/mman.h>
#include <assert.h>
#include <err.h>
#include <errno.h>
#include <math.h>
#include <sqlite3.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define ROUND_UP_PAGE(x) (((x) + 4095ul) & ~4095ul)

#define MAGIC 0xbb8d4fde1557ab1ful

typedef unsigned char uint8_t;

#define NR_HEADS 524243

struct hash_entry {
	uint8_t aliases[16];
	uint8_t stackEscape;
};

struct header {
	unsigned long magic;
	struct {
		off_t offset;
		int nr_slots;
	} heads[NR_HEADS];
};

struct output_file {
	int fd;
	size_t allocated;
	size_t mapping_size;
	unsigned long mapping;
};

static int
hash_rip(unsigned long h)
{
	while (h >= NR_HEADS)
		h = (h / NR_HEADS) ^ (h % NR_HEADS);
	return h;
}

static int
open_output(const char *fname, struct output_file *of)
{
	memset(of, 0, sizeof(*of));

	char *tmp_fname;
	int cntr;
	int fd;
	for (cntr = 0; ; cntr++) {
		tmp_fname = 0;
		if (asprintf(&tmp_fname, "%s.%d.tmp", fname, cntr) < 0)
			err(1, "asprintf()");
		fd = open(tmp_fname, O_RDWR | O_CREAT | O_EXCL, 0600);
		if (fd >= 0)
			break;
		if (errno != EEXIST) {
			free(tmp_fname);
			return -1;
		}
		free(tmp_fname);
	}
	size_t sz = sizeof(header);
	void *mapping;
	sz = ROUND_UP_PAGE(sz);
	if (ftruncate(fd, sz) < 0)
		goto failed;
	mapping = mmap(NULL, sz, PROT_READ|PROT_WRITE,
		       MAP_SHARED, fd, 0);
	if (mapping == MAP_FAILED)
		goto failed;
	if (rename(tmp_fname, fname) < 0) {
		munmap(mapping, sz);
		goto failed;
	}

	of->fd = fd;
	of->allocated = sizeof(header);
	of->mapping_size = sz;
	of->mapping = (unsigned long)mapping;

	/* We deliberately don't set the magic number here; that's
	   only done once the rest of the file is finished. */
	return 0;

failed:
	close(fd);
	unlink(tmp_fname);
	free(tmp_fname);
	return -1;
}

static void
allocate_hash_chain(struct output_file *f, int idx, int len)
{
	assert(len > 0);
	struct header *h = (struct header *)f->mapping;
	h->heads[idx].offset = f->allocated;
	unsigned needed = (sizeof(struct hash_entry) + 8) * len;
	needed = (needed + 7) & ~7u;
	f->allocated += needed;
}

static void
add_entry(struct output_file *f, int idx, int max_this_slot, unsigned long rip, int stackEscape, const uint8_t *alias)
{
	assert(max_this_slot > 0);
	if (f->allocated > f->mapping_size) {
		if (ftruncate(f->fd, f->allocated) < 0)
			err(1, "expanding output file to %zd bytes", f->allocated);
		void *nmap = mmap(NULL, ROUND_UP_PAGE(f->allocated), PROT_READ|PROT_WRITE,
				  MAP_SHARED, f->fd, 0);
		if (nmap == MAP_FAILED)
			err(1, "re-mapping expanded output file");
		munmap((void *)f->mapping, f->mapping_size);
		f->mapping_size = ROUND_UP_PAGE(f->allocated);
		f->mapping = (unsigned long)nmap;
	}

	struct header *h = (struct header *)f->mapping;
	assert(h->heads[idx].offset != 0);
	assert(h->heads[idx].offset >= (off_t)sizeof(header));
	assert(h->heads[idx].offset + sizeof(struct hash_entry) * max_this_slot <= f->allocated);
	assert(h->heads[idx].nr_slots < max_this_slot);
	unsigned long *rip_area = (unsigned long *)(f->mapping + h->heads[idx].offset);
	struct hash_entry *entries = (struct hash_entry *)(f->mapping + h->heads[idx].offset + 8 * max_this_slot);
	struct hash_entry *he = &entries[h->heads[idx].nr_slots];
	rip_area[h->heads[idx].nr_slots] = rip;
	memcpy(he->aliases, alias, 16);
	he->stackEscape = stackEscape;
	h->heads[idx].nr_slots++;
}

static void
flush_output_file(struct output_file *f)
{
	struct header *h = (struct header *)f->mapping;
	h->magic = MAGIC;
}

int
main(int argc, char *argv[])
{
	if (argc != 3)
		errx(1, "expected two arguments, an input DB and an out put file");
	const char *db_fname = argv[1];
	const char *output_fname = argv[2];
	sqlite3 *database = NULL;
	int rc = sqlite3_open_v2(db_fname, &database, SQLITE_OPEN_READONLY, NULL);
	if (rc != SQLITE_OK) {
		if (database)
			errx(1, "opening %s: %s", db_fname, sqlite3_errmsg(database));
		else
			errx(1, "opening %s: %d", db_fname, rc);
	}

	struct output_file output;
	if (open_output(output_fname, &output) < 0)
		err(1, "opening %s", output_fname);

	/* First, figure out how long all of the hash chains are going to be. */
	sqlite3_stmt *stmt;
	if (sqlite3_prepare_v2(
		    database,
		    "SELECT rip FROM instructionAttributes",
		    -1,
		    &stmt,
		    NULL) != SQLITE_OK)
		errx(1, "preparing first SQL statement: %s", sqlite3_errmsg(database));
	int hash_chain_lengths[NR_HEADS];
	int tot_nr_entries = 0;
	memset(hash_chain_lengths, 0, sizeof(hash_chain_lengths));
	while ((rc = sqlite3_step(stmt)) == SQLITE_ROW) {
		unsigned long rip = sqlite3_column_int64(stmt, 0);
		if (rip == 0)
			errx(1, "RIP of 0 in the database?");
		int h = hash_rip(rip);
		hash_chain_lengths[h]++;
		tot_nr_entries++;
	}
	if (rc != SQLITE_DONE)
		errx(1, "determining hash table shape: %s", sqlite3_errmsg(database));

	/* And some simple statistics... */
	int longest_length = -1;
	long len2 = 0;
	int nr_empty = 0;
	for (int i = 0; i < NR_HEADS; i++) {
		if (hash_chain_lengths[i] > longest_length)
			longest_length = hash_chain_lengths[i];
		len2 += hash_chain_lengths[i] * hash_chain_lengths[i];
		if (hash_chain_lengths[i] == 0)
			nr_empty++;
	}
	printf("Average chain length %f, longest %d, average2 length %f, %f%% empty\n",
	       (double)tot_nr_entries / NR_HEADS,
	       longest_length,
	       sqrt(len2 / (double)NR_HEADS),
	       nr_empty * 100.0 / NR_HEADS);

	/* Now allocate space in the file */
	for (int i = 0; i < NR_HEADS; i++) {
		if (hash_chain_lengths[i] != 0)
			allocate_hash_chain(&output, i, hash_chain_lengths[i]);
	}

	/* Now we can actually populate the file. */
	if (sqlite3_prepare_v2(
		    database,
		    "SELECT rip, alias0, alias1, alias2, alias3, alias4, alias5, alias6, alias7, alias8, alias9, alias10, alias11, alias12, alias13, alias14, alias15, stackEscape FROM instructionAttributes",
		    -1,
		    &stmt,
		    NULL) != SQLITE_OK)
		errx(1, "preparing SQL statement: %s", sqlite3_errmsg(database));

	while ((rc = sqlite3_step(stmt)) == SQLITE_ROW) {
		unsigned long rip = sqlite3_column_int64(stmt, 0);
		uint8_t alias[16];
		for (int i = 0; i < 16; i++)
			alias[i] = sqlite3_column_int(stmt, i + 1);
		int stackEscape = sqlite3_column_int(stmt, 17);
		int idx = hash_rip(rip);
		add_entry(&output, idx, hash_chain_lengths[idx], rip, stackEscape, alias);
	}
	if (rc != SQLITE_DONE)
		errx(1, "advancing SQL query: %s", sqlite3_errmsg(database));
	flush_output_file(&output);

	return 0;
}
