#include <pthread.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

#include "test.h"

#ifndef NR_PTRS
#define NR_PTRS 100
#endif

static int *volatile global_ptrs[NR_PTRS];

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
		read_cntr++;
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
	int forever = 0;
	int del;

	srandom(start_time);

	pthread_create(&thr, NULL, thr_main, NULL);
	for (idx = 0; idx < NR_PTRS; idx++)
		global_ptrs[idx] = &t;

	if (getenv("SOS22_RUN_FOREVER"))
		forever = 1;

	if (NR_PTRS < 5000) {
		del = 20;
	} else if (NR_PTRS < 100000) {
		del = 60;
	} else {
		del = 240;
	}
	while (forever || time(NULL) < start_time + del) {
		idx = random() % NR_PTRS;
		STOP_ANALYSIS();
		global_ptrs[idx] = NULL;
		STOP_ANALYSIS();
		global_ptrs[idx] = &t;
		STOP_ANALYSIS();
		write_cntr++;
	}

	force_quit = true;
	pthread_join(thr, NULL);

	printf("Survived, %d read events and %d write events\n",
	       read_cntr, write_cntr);
	return 0;
}
