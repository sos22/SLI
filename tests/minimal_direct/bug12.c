#include <pthread.h>
#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

#include "test.h"

#define NR_PTRS 100
static volatile int global;

static void *
thr_main(void *ign)
{
	int x1;
	int x2;
	int x3;
	int x4;
	int x5;
	int x6;
	int x7;
	int x8;
	int x9;
	while (!force_quit) {
		STOP_ANALYSIS();
		x1 = global;
		x2 = global;
		x3 = global;
		x4 = global;
		x5 = global;
		x6 = global;
		x7 = global;
		x8 = global;
		x9 = global;
		assert(!(x1 == 0 && x2 == 1 && x3 == 2 &&
			 x4 == 3 && x5 == 4 && x6 == 5 &&
			 x7 == 6 && x8 == 7 && x9 == 8));
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
	int forever = 0;

	pthread_create(&thr, NULL, thr_main, NULL);

	if (getenv("SOS22_RUN_FOREVER"))
		forever = 1;

	while (forever || time(NULL) < start_time + 10) {
		STOP_ANALYSIS();
		global = 0;
		global = 1;
		global = 2;
		global = 3;
		global = 4;
		global = 5;
		global = 6;
		global = 7;
		global = 8;
		STOP_ANALYSIS();
		write_cntr++;
	}

	force_quit = true;
	pthread_join(thr, NULL);

	printf("Survived, %d read events and %d write events\n",
	       read_cntr, write_cntr);
	return 0;
}
