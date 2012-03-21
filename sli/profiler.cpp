#include <assert.h>
#include <execinfo.h>
#include <setjmp.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <set>
#include <vector>

#include "timers.hpp"

#define NR_BACKTRACE_ENTRIES 4
#define BACKTRACE_SKIP 5

#define MAX_NR_PROFILE_ENTRIES 4096
#define NR_HASH_HEADS 511

class ProfTimer : public Timer {
public:
	void fired();
};

static ProfTimer profTimer;

/* It'd be nice to use BacktraceProfiler here, but that uses the main
 * heap, which isn't a great idea from a signal handler. */
struct profile_entry {
	/* This is used for both hash chaining and the free list. */
	struct profile_entry *next;

	unsigned long hash;
	int cntr;
	int nr_entries_in_trace;
	void *content[NR_BACKTRACE_ENTRIES];
};

static struct profile_entry pe_heap[MAX_NR_PROFILE_ENTRIES];
static struct profile_entry *next_alloc;
static struct profile_entry *hash_heads[NR_HASH_HEADS];
static unsigned long total_nr_samples;
static unsigned long samples_lost;
static unsigned long samples_discarded;
static bool collect_samples;

static bool in_backtrace;
static jmp_buf backtrace_recovery_jmpbuf;
static unsigned long nr_recovered_segvs;

static unsigned long
hash_backtrace(const void *const*trace, int nr_items)
{
	unsigned long acc = 0;
	int i;
	/* Just use a random prime to permute things as we walk along
	 * the trace. */
	for (i = 0; i < nr_items; i++)
		acc = acc * 10036711 + (unsigned long)trace[i];
	return acc;
}

static bool
profile_entry_doesnt_match(const void *const *trace, int nr_items, const struct profile_entry *pe)
{
	if (pe->nr_entries_in_trace != nr_items ||
	    memcmp(pe->content, trace, sizeof(trace[0]) * nr_items))
		return true;
	else
		return false;
}

static struct profile_entry *
find_profile_entry(const void *const *stack, int stack_size, unsigned long hash,
		   struct profile_entry ***ppprev)
{
	struct profile_entry *pe;
	struct profile_entry **pprev;
	pprev = &hash_heads[hash % NR_HASH_HEADS];
	pe = *pprev;
	while (pe != NULL &&
	       (pe->hash != hash || profile_entry_doesnt_match(stack,
							       stack_size,
							       pe))) {
		pprev = &pe->next;
		pe = *pprev;
	}
	if (ppprev)
		*ppprev = pprev;
	return pe;
}

void
ProfTimer::fired()
{
	if (!collect_samples)
		return;

	void *trace[NR_BACKTRACE_ENTRIES + BACKTRACE_SKIP];
	unsigned long hash;
	struct profile_entry *pe;
	int cntr;

	/* See handle_sigsegv() for explanation of what's going on
	 * here */
	in_backtrace = true;
	if (sigsetjmp(backtrace_recovery_jmpbuf, 1)) {
		in_backtrace = false;
		nr_recovered_segvs++;
		return;
	}
	cntr = backtrace(trace, NR_BACKTRACE_ENTRIES + BACKTRACE_SKIP);
	in_backtrace = false;
	if (cntr <= BACKTRACE_SKIP)
		return;

	total_nr_samples++;

	hash = hash_backtrace(trace + BACKTRACE_SKIP, cntr - BACKTRACE_SKIP);
	pe = find_profile_entry(trace + BACKTRACE_SKIP, cntr - BACKTRACE_SKIP, hash, NULL);
	if (pe) {
		pe->cntr++;
		return;
	}

	pe = next_alloc;
	if (!pe) {
		samples_lost++;
		return;
	}
	next_alloc = pe->next;

	pe->next = hash_heads[hash % NR_HASH_HEADS];
	pe->hash = hash;
	pe->cntr = 1;
	pe->nr_entries_in_trace = cntr - BACKTRACE_SKIP;
	memcpy(pe->content, trace + BACKTRACE_SKIP, (cntr - BACKTRACE_SKIP) * sizeof(pe->content[0]));
	hash_heads[hash % NR_HASH_HEADS] = pe;
}

static void
handle_sigsegv(int signr)
{
	/* backtrace() can sometimes segfault if there's code on the
	 * stack without frame pointers (e.g. all of libstdc++).  The
	 * correct fix is to make it not do that, but since this is
	 * just a quick debug hack, we work around it by just
	 * longjmping to somewhere sane if we get into trouble.
	 */
	if (!in_backtrace) {
		/* Uh oh.  Force a real segv. */
		*(unsigned *)0xf001 = 5;
		abort();
	}
	siglongjmp(backtrace_recovery_jmpbuf, 1);
	abort();
}

void
initialise_profiling()
{
	int i;
	for (i = 0; i < MAX_NR_PROFILE_ENTRIES; i++) {
		pe_heap[i].next = &pe_heap[i+1];
		pe_heap[i].hash = 0;
		pe_heap[i].cntr = 0;
		pe_heap[i].nr_entries_in_trace = 0;
	}
	pe_heap[i-1].next = NULL;
	next_alloc = &pe_heap[0];

	profTimer.interval = 0.01;
	profTimer.nextDue = now() + 0.01;

	signal(SIGSEGV, handle_sigsegv);

	profTimer.schedule();
}

void
start_profiling()
{
	collect_samples = true;
}

void
stop_profiling()
{
	collect_samples = false;
}

static void
zap_profile_entry(const std::vector<void *> &stack)
{
	void *content[stack.size()];
	for (unsigned x = 0; x < stack.size(); x++)
		content[x] = stack[x];
	unsigned long hash = hash_backtrace(content, stack.size());
	struct profile_entry **pprev;
	struct profile_entry *pe = find_profile_entry(content, stack.size(), hash, &pprev);
	if (!pe) {
		/* Because otherwise we won't have been called. */
		abort();
	}

	samples_discarded += pe->cntr;
	pe->cntr = 0;

	assert(*pprev == pe);
	*pprev = pe->next;
	pe->next = next_alloc;
	next_alloc = pe;
}

void
dump_profiling_data()
{
	assert(!collect_samples);

	typedef std::vector<void *> stack_t;
	typedef std::pair<unsigned long, stack_t> set_entry_t;

	std::set<set_entry_t> theProfile;

	for (int x = 0; x < MAX_NR_PROFILE_ENTRIES; x++) {
		if (pe_heap[x].cntr == 0)
			continue;
		profile_entry *pe = &pe_heap[x];
		stack_t stack;
		stack.resize(pe->nr_entries_in_trace);
		for (int y = 0; y < pe->nr_entries_in_trace; y++)
			stack[y] = pe->content[y];
		theProfile.insert(set_entry_t(pe->cntr, stack));
	}

	printf("Profile:\n");
	for (auto it = theProfile.begin(); it != theProfile.end(); it++) {
		printf("\t%f ", double(it->first) / total_nr_samples);
		for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
			if (it2 != it->second.begin())
				printf(", ");
			printf("%p", *it2);
		}
		printf("\n");
	}
	printf("\t%f <lost>\n", double(samples_lost) / total_nr_samples);
	printf("\t%f <discard>\n", double(samples_discarded) / total_nr_samples);
	printf("\t%f <recovered segv>\n", double(nr_recovered_segvs) / total_nr_samples);
	printf("\t%ld total samples\n", total_nr_samples);

	/* Zap the least popular entries, so that there's room for
	 * some more to appear. */
	int cntr;
	if (theProfile.size() >= MAX_NR_PROFILE_ENTRIES * 3 / 4)
		cntr = theProfile.size() - MAX_NR_PROFILE_ENTRIES * 3 / 4;
	else
		cntr = 0;
	for (auto it = theProfile.begin(); it != theProfile.end() && cntr != 0; it++) {
		zap_profile_entry(it->second);
		cntr--;
	}
}
