#include <pthread.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "test.h"

#define NR_PTRS 100
#define NR_READ_THREADS 32
#define NR_WRITE_THREADS 32
static int *volatile global_ptrs[NR_PTRS];

static volatile bool force_quit1, force_quit2;

static void *
read_thread(void *ign)
{
	while (!force_quit2) {
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

static void *
write_thread(void *ign)
{
	int t;
	int idx;
	while (!force_quit1) {
		idx = random() % NR_PTRS;
		STOP_ANALYSIS();
		global_ptrs[idx] = NULL;
		STOP_ANALYSIS();
		global_ptrs[idx] = &t;
		STOP_ANALYSIS();
		write_cntr++;
	}
	return NULL;
}

int
main()
{
	pthread_t read_thr[NR_READ_THREADS];
	pthread_t write_thr[NR_WRITE_THREADS];
	int i;

	for (i = 0; i < NR_READ_THREADS; i++)
		pthread_create(&read_thr[i], NULL, read_thread, NULL);
	for (i = 0; i < NR_WRITE_THREADS; i++)
		pthread_create(&write_thr[i], NULL, write_thread, NULL);

	if (getenv("SOS22_RUN_FOREVER")) {
		while (1)
			sleep(10);
	}

	sleep(10);

	force_quit2 = true;
	for (i = 0; i < NR_READ_THREADS; i++)
		pthread_join(read_thr[i], NULL);
	force_quit1 = true;
	for (i = 0; i < NR_WRITE_THREADS; i++)
		pthread_join(write_thr[i], NULL);

	printf("Survived, %d read events and %d write events\n",
	       read_cntr, write_cntr);
	return 0;
}
