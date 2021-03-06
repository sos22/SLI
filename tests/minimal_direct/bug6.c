/* context */
#include <pthread.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

#include "test.h"

static int *volatile global_ptr1;
static int *volatile global_ptr2;

static void
f(int *volatile *ptr)
{
	if (*ptr)
		**ptr = 5;
}

static void *
thr_main(void *ign)
{
	bool r;
	while (!force_quit) {
		r = random() % 1000 == 0;
		if (r) {
			STOP_ANALYSIS();
			f(&global_ptr1);
		} else {
			STOP_ANALYSIS();
			f(&global_ptr2);
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
	int t;
	int forever = !!getenv("SOS22_RUN_FOREVER");

	global_ptr1 = &t;
	global_ptr2 = &t;
	pthread_create(&thr, NULL, thr_main, NULL);

	time_t start_time = time(NULL);

	while (forever || time(NULL) < start_time + 10) {
		STOP_ANALYSIS();
		global_ptr1 = &t;
		STOP_ANALYSIS();
		usleep(1000);
		STOP_ANALYSIS();
		global_ptr1 = NULL;
		STOP_ANALYSIS();
		write_cntr++;
	}

	force_quit = true;
	pthread_join(thr, NULL);

	printf("Survived, %d read events and %d write events\n",
	       read_cntr, write_cntr);

	return 0;
}
