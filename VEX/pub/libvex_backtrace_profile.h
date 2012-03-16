/* Simple thing for building up a histogram of backtraces, showing
   roughly where a particular function is most often called from. */
#ifndef LIBVEX_BACKTRACE_PROFILE_H__
#define LIBVEX_BACKTRACE_PROFILE_H__

#include <stdio.h>
#include <map>
#include <vector>

class BacktraceProfile {
	typedef std::vector<void *> key_t;
	std::map<key_t, unsigned long> histogram;
	int nr_stack_entries;
	int autodump_freq;
	const char *banner;

	long tot_nr_samples;
public:
	void sample();
	void dump(FILE *f);
	BacktraceProfile(int _nr_stack_entries, int _autodump_freq, const char *_banner)
		: nr_stack_entries(_nr_stack_entries),
		  autodump_freq(_autodump_freq),
		  banner(_banner),
		  tot_nr_samples(0)
	{}
};

#endif /* !LIBVEX_BACKTRACE_PROFILE_H__ */
