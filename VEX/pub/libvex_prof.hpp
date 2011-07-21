#ifndef LIBVEX_PROF_HPP__
#define LIBVEX_PROF_HPP__

#if MANUAL_PROFILING
class ProfilingSite {
public:
	const char *name;
	unsigned long accumulated_ticks;
	unsigned long nr_sites;
	ProfilingSite *next;
	bool live;
	static ProfilingSite *head_prof_site;
	ProfilingSite(const char *_name)
		: name(_name), accumulated_ticks(0), nr_sites(0), live(false)
	{
		next = head_prof_site;
		head_prof_site = this;
	}
};

class SetProfiling {
public:
	static unsigned long rdtsc() {
		unsigned long rax, rdx;
		__asm__ ( "rdtsc\n"
			  : "=a" (rax), "=d" (rdx) );
		return rax | (rdx << 32);
	}
	ProfilingSite *site;
	unsigned long start;
	bool doit;
	SetProfiling(ProfilingSite *_site)
		: site(_site)
	{
		doit = !site->live;
		if (doit) {
			site->live = true;
			start = rdtsc();
		} else {
			start = 0;
		}
	}
	~SetProfiling()
	{
		if (doit) {
			site->accumulated_ticks += rdtsc() - start;
			site->nr_sites++;
			site->live = false;
		}
	}
};

#define __set_profiling(name)						\
	static ProfilingSite __prof_site_ ## name ( #name );		\
	SetProfiling __set_prof_site_ ## __LINE__ (&__prof_site_ ## name);

#else /* if !MANUAL_PROFILING */
#define __set_profiling(name)
#endif

#endif /* !LIBVEX_PROF_HPP__ */
