/* Simple thing for experimenting with various forms of static
   analysis. */
#include <ctype.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>

#include "libvex_alloc.h"
#include "libvex_ir.h"
#include "libvex_guest_offsets.h"
#include "sli.h"
#include "map.h"
#include "oracle.hpp"

#include <map>

/* Read a whole line into the GC heap */
static char *
read_line(FILE *f)
{
	size_t acc_size;
	size_t used;
	char *acc;
	int c;

	acc_size = 128;
	acc = (char *)LibVEX_Alloc_Bytes(acc_size);
	used = 0;
	while (1) {
		c = fgetc(f);
		if (c == '\n' || c == EOF)
			break;
		acc[used] = c;
		used++;
		if (used == acc_size) {
			acc_size *= 2;
			acc = (char *)LibVEX_realloc(&main_heap, acc, acc_size);
		}
	}
	if (c == EOF) {
		if (used == 0 || ferror(f))
			return NULL;
	}
	acc[used] = 0;
	return acc;
}

class BadParseException {
};

class Word : public GarbageCollected<Word>, public Named {
protected:
	char *mkName() const { return strdup(content); }
public:
	char *content;
	Word(const char *c, int len) {
		content = (char *)LibVEX_Alloc_Bytes(len + 1);
		memcpy(content, c, len);
		content[len] = 0;
	}
	bool operator==(const char *p) const {
		return strcmp(content, p) == 0;
	}
	operator unsigned long() const {
		if (!this) {
			printf("Not enough arguments\n");
			throw BadParseException();
		}
		errno = 0;
		char *end;
		unsigned long r = strtol(content, &end, 0);
		if (errno != 0 || *end != 0) {
			printf("Expected number; got %s\n", content);
			throw BadParseException();
		}
		return r;
	}
	operator VexRip() const {
		return VexRip::invent_vex_rip(*this);
	}
	void visit(HeapVisitor &hv) { hv(content); }
	NAMED_CLASS
};

static Word **
find_words(char *command)
{
	int i;
	int nr_words;
	int j;

	nr_words = 0;
	i = 0;
	while (1) {
		/* Find the start of the current word. */
		while (isspace(command[i]))
			i++;
		if (command[i] == 0)
			break;
		/* We have another word. */
		nr_words++;
		/* And now find its end */
		while (!isspace(command[i]) && command[i])
			i++;
	}

	Word **res;
	res = (Word **)__LibVEX_Alloc_Ptr_Array(&main_heap, nr_words + 1);
	j = 0;
	i = 0;
	nr_words = 0;
	while (1) {
		/* Find the start of the word */
		while (isspace(command[i]))
			i++;
		if (command[i] == 0)
			break;
		/* Now find the end. */
		j = i;
		while (!isspace(command[j]) && command[j])
			j++;
		res[nr_words] = new Word(command + i, j - i);
		nr_words++;
		i = j;
	}
	res[nr_words] = NULL;
	return res;
}

static void
list_heads(Oracle *oracle)
{
	std::vector<VexRip> f;

	oracle->getFunctions(f);
	for (auto it = f.begin();
	     it != f.end();
	     it++)
		printf("%s\n", it->name());
}

static std::vector<VexRip> newHeads;

static void
run_command(VexPtr<Oracle> &oracle, GarbageCollectionToken token)
{
	LibVEX_maybe_gc(ALLOW_GC);

	printf("\n> ");
	fflush(stdout);
	char *command = read_line(stdin);
	if (!command)
		exit(0);
	Word **words = find_words(command);	

	if (*words[0] == "add_root") {
		newHeads.push_back(*words[1]);
	} else if (*words[0] == "doit") {
		oracle->discoverFunctionHeads(oracle, newHeads, token);
	} else if (*words[0] == "list_heads") {
		list_heads(oracle);
	} else if (*words[0] == "liveness") {
		Oracle::Function f(*words[1]);
		printf("%s\n", f.liveOnEntry(f.rip, false).name());
	} else if (*words[0] == "alias") {
		Oracle::Function f(*words[1]);
		Oracle::RegisterAliasingConfiguration alias = f.aliasConfigOnEntryToInstruction(*words[2]);
		printf("Alias table for %lx:%lx:\n", (unsigned long)*words[1],
		       (unsigned long)*words[2]);
		alias.prettyPrint(stdout);
	} else {
		printf("Unknown command %s\n", words[0]->content);
	}
}

int
main(int argc, char *argv[])
{
	init_sli();

	VexPtr<MachineState> ms(MachineState::readCoredump(argv[1]));
	VexPtr<Oracle> oracle(new Oracle(ms, NULL, argv[2]));

	while (1) {
		try {
			run_command(oracle, ALLOW_GC);
		} catch (BadParseException e) {
		}
	}
}
