/* non_race */
#include <pthread.h>
#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

static int volatile global1;
static int volatile global2;
static pthread_mutex_t mux = PTHREAD_MUTEX_INITIALIZER;

#include "test.h"

static void *
thr_main(void *ign)
{
	while (!force_quit) {
		int v1;
		int v2;
		STOP_ANALYSIS();
		pthread_mutex_lock(&mux);
		v1 = global1;
		pthread_mutex_unlock(&mux);
		pthread_mutex_lock(&mux);
		v2 = global2;
		pthread_mutex_unlock(&mux);
		assert(v1 == v2);
		STOP_ANALYSIS();
		usleep(1000);
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
		pthread_mutex_lock(&mux);
		global1 = 5;
		STOP_ANALYSIS();
		global2 = 5;
		pthread_mutex_unlock(&mux);
		STOP_ANALYSIS();
		usleep(1000);
		STOP_ANALYSIS();
		pthread_mutex_lock(&mux);
		global1 = 7;
		global2 = 7;
		pthread_mutex_unlock(&mux);
		STOP_ANALYSIS();
		write_cntr++;
	}

	force_quit = true;
	pthread_join(thr, NULL);
	printf("Survived, %d read events and %d write events\n", read_cntr, write_cntr);
	return 0;
}
