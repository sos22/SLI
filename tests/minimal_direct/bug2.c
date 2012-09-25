#include <pthread.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

static int nr_read_events;
static int nr_write_events;

#define NR_PTRS 100
static int *volatile global_ptrs[NR_PTRS];

static volatile bool force_quit;

#define STOP_ANALYSIS()					\
	do {						\
		int cntr;				\
		for (cntr = 0; cntr < 1000; cntr++)	\
			asm ("nop");			\
	} while (0)

static void *
thr_main(void *ign)
{
	while (!force_quit) {
		int idx = random() % NR_PTRS;
		int *p;
		STOP_ANALYSIS();
		p = global_ptrs[idx];
		if (p) {
			p = global_ptrs[idx];
			*p = 5;
		}
		STOP_ANALYSIS();
		nr_read_events++;
	}
	return NULL;
}

int
main()
{
	pthread_t thr;
	time_t start_time = time(NULL);
	int t;
	int idx;
	pthread_create(&thr, NULL, thr_main, NULL);
	for (idx = 0; idx < NR_PTRS; idx++)
		global_ptrs[idx] = &t;

	while (time(NULL) < start_time + 10) {
		idx = random() % NR_PTRS;
		STOP_ANALYSIS();
		global_ptrs[idx] = NULL;
		STOP_ANALYSIS();
		global_ptrs[idx] = &t;
		STOP_ANALYSIS();
		nr_write_events++;
	}

	force_quit = true;
	pthread_join(thr, NULL);

	printf("Survived, %d read events and %d write events\n",
	       nr_read_events, nr_write_events);
	return 0;
}
