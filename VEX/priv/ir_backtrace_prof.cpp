#include "libvex_backtrace_profile.h"

#include <set>

#include <execinfo.h>

void
BacktraceProfile::sample(void)
{
	void *trace[nr_stack_entries+1];
	int nr_back;
	nr_back = ::backtrace(trace, nr_stack_entries+1);
	key_t key;
	key.resize(nr_back-1);
	for (int x = 0; x < nr_back-1; x++)
		key[x] = trace[x+1];
	histogram[key]++;
	tot_nr_samples++;

	if (autodump_freq > 0 &&
	    tot_nr_samples % autodump_freq == 0)
		dump(stdout);
}

void
BacktraceProfile::dump(FILE *f)
{
	fputs(banner, f);
	std::set<std::pair<unsigned, key_t> > swapped;
	for (auto it = histogram.begin(); it != histogram.end(); it++)
		swapped.insert(std::pair<unsigned, key_t>(it->second, it->first));
	for (auto it = swapped.begin(); it != swapped.end(); it++) {
		unsigned cntr = it->first;
		const key_t &val(it->second);
		fprintf(f, "\t%f\t\t", cntr / double(tot_nr_samples));
		for (auto it = val.begin(); it != val.end(); it++) {
			if (it != val.begin())
				fprintf(f, ", ");
			fprintf(f, "%p", *it);
		}
		fprintf(f, "\n");
	}
}
