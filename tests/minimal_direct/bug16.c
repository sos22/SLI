/* A variant of bug15 in whcih we can't handle the sync. */
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "test.h"

static int *volatile global_ptr;
static pthread_mutex_t mux = PTHREAD_MUTEX_INITIALIZER;

static void *
thr_main(void *ign)
{
	while (1) {
		int *p;
		pthread_mutex_lock(&mux);
		STOP_ANALYSIS();
		p = global_ptr;
		if (p) {
			p = global_ptr;
			*p = 5;
		}
		STOP_ANALYSIS();
		pthread_mutex_unlock(&mux);
		read_cntr++;
		STOP_ANALYSIS();
	}
	return NULL;
}

int
main()
{
	pthread_t thr;
	int forever = 0;

	pthread_create(&thr, NULL, thr_main, NULL);

	time_t start_time = time(NULL);

	if (getenv("SOS22_RUN_FOREVER"))
		forever = 1;
	int t;
	while (forever || time(NULL) < start_time + 10) {
		STOP_ANALYSIS();
		global_ptr = &t;
		STOP_ANALYSIS();

		usleep(1000000);

		pthread_mutex_lock(&mux);
		STOP_ANALYSIS();
		global_ptr = NULL;
		STOP_ANALYSIS();
		pthread_mutex_unlock(&mux);
		write_cntr++;
	}

	printf("Survived, %d read events and %d write events\n", read_cntr, write_cntr);
	return 0;
}
