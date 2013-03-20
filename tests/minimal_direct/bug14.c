/* double_free */
/* Aim of this one is to demonstrate that you can do something
   interesting with double-frees. */
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>

#include "test.h"

static void *volatile the_ptr;

static void *
thr_main(void *ign)
{
	while (!force_quit) {
		STOP_ANALYSIS();
		free(the_ptr);
		the_ptr = NULL;
		STOP_ANALYSIS();
		read_cntr++;
		usleep(1000);
	}

	return NULL;
}

int
main()
{
	pthread_t thr1;
	pthread_t thr2;
	time_t start_time = time(NULL);
	int forever = 0;

	pthread_create(&thr1, NULL, thr_main, NULL);
	usleep(100);
	pthread_create(&thr2, NULL, thr_main, NULL);

	if (getenv("SOS22_RUN_FOREVER"))
		forever = 1;

	while (forever || time(NULL) < start_time + 10) {
		STOP_ANALYSIS();
		if (!the_ptr)
			the_ptr = malloc(64);
		STOP_ANALYSIS();
		write_cntr++;
	}

	force_quit = true;
	pthread_join(thr1, NULL);
	pthread_join(thr2, NULL);

	printf("Survived, %d read events and %d write events\n",
	       read_cntr, write_cntr);
	return 0;
}
