/* multi_variable */
#include <pthread.h>
#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

static int volatile global1;
static int volatile global2;

#include "test.h"

static void *
thr_main(void *ign)
{
	while (!force_quit) {
		int v1;
		int v2;
		STOP_ANALYSIS();
		v1 = global1;
		v2 = global2;
		assert(v1 == v2);
		STOP_ANALYSIS();
		usleep(500);
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
	if (getenv("SOS22_RUN_FOREVER"))
		forever = 1;

	global1 = 99;
	global2 = 99;

	pthread_create(&thr, NULL, thr_main, NULL);

	while (forever || time(NULL) < start_time + 10) {
		STOP_ANALYSIS();
		global1 = 5;
		STOP_ANALYSIS();
		global2 = 5;
		STOP_ANALYSIS();
		usleep(500);
		STOP_ANALYSIS();
		global1 = 7;
		global2 = 7;
		STOP_ANALYSIS();
		write_cntr++;
	}

	force_quit = true;
	pthread_join(thr, NULL);
	printf("Survived, %d read events and %d write events\n", read_cntr, write_cntr);
	return 0;
}
