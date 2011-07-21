#include <stddef.h>
#include <stdio.h>

#include <algorithm>
#include <vector>

#include "libvex_prof.hpp"

#if MANUAL_PROFILING
ProfilingSite *ProfilingSite::head_prof_site;

static class __profiling_dump_class {
public:
	unsigned long start_of_day;
	__profiling_dump_class() : start_of_day(SetProfiling::rdtsc()) {}
	void dump_profile();
	~__profiling_dump_class() { dump_profile(); }
} __do_profiling_dump;

void __profiling_dump_class::dump_profile()
{
	unsigned long total_time = SetProfiling::rdtsc() - start_of_day;
	std::vector<std::pair<unsigned long, ProfilingSite *> > sites;
	ProfilingSite *cursor;

	for (cursor = ProfilingSite::head_prof_site;
	     cursor != NULL;
	     cursor = cursor->next)
		sites.push_back(std::pair<unsigned long, ProfilingSite *>(cursor->accumulated_ticks, cursor));

	std::sort(sites.begin(), sites.end());
	for (unsigned x = 0; x < sites.size(); x++) {
		cursor = sites[x].second;
		printf("%s: %ld invocations, each of %f ticks; %f of total runtime\n",
		       cursor->name, cursor->nr_sites,
		       cursor->accumulated_ticks / (double)cursor->nr_sites,
		       (double)cursor->accumulated_ticks / total_time); 
	}
}

#endif /* MANUAL_PROFILING */
