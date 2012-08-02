#include <pthread.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

static int volatile global1;
static int volatile global2;

static volatile bool force_quit;

#define STOP_ANALYSIS()					\
	asm (".fill 100,1,0x90\n")

static void *
thr_main(void *ign)
{
	while (!force_quit) {
		int v1;
		int v2;
		STOP_ANALYSIS();
		v1 = global1;
		v2 = global2;
		if (v1 != v2)
			*(unsigned long *)0xf001 = 5;
		STOP_ANALYSIS();
	}
	return NULL;
}

int
main()
{
	pthread_t thr;
	time_t start_time = time(NULL);

	pthread_create(&thr, NULL, thr_main, NULL);

	while (time(NULL) < start_time + 10) {
		STOP_ANALYSIS();
		global1 = 5;
		global2 = 5;
		STOP_ANALYSIS();
		usleep(10000);
		STOP_ANALYSIS();
		global1 = 7;
		global2 = 7;
		STOP_ANALYSIS();
		usleep(10000);
	}

	force_quit = true;
	pthread_join(thr, NULL);
	return 0;
}
