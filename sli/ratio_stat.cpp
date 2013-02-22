#include "sli.h"

#ifndef NDEBUG
static std::set<ratio_stat *> all_stats;

ratio_stat::ratio_stat(const char *fmt, ...)
{
	va_list args;
	int i;
	char *n;
	va_start(args, fmt);
	i = vasprintf(&n, fmt, args);
	va_end(args);
	if (i < 0) {
		errx(1, "ratio_stat(%s)", fmt);
	}
	name = n;
	reset();
	all_stats.insert(this);
}

ratio_stat::~ratio_stat()
{
	print();
	free((void *)name);
	all_stats.erase(this);
}

void
ratio_stat::print() const
{
	if (denominator == 0) {
		printf("%60s: inf\n", name);
	} else {
		printf("%60s: %f%%          (%8ld/%8ld)\n",
		       name,
		       100 * (double)numerator / denominator,
		       numerator,
		       denominator);
	}
}

void
ratio_stat::reset()
{
	numerator = 0;
	denominator = 0;
}

void
dump_stats()
{
	for (auto it = all_stats.begin(); it != all_stats.end(); it++) {
		(*it)->print();
	}
}
void
reset_stats()
{
	for (auto it = all_stats.begin(); it != all_stats.end(); it++) {
		(*it)->reset();
	}
}
#endif
