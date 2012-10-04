#include <pthread.h>
#include <stdio.h>
#include <time.h>
#include <unistd.h>

#define STOP_ANALYSIS()					\
	asm (".fill 100,1,0x90\n")

static int *volatile global_ptr;

static void *
thr_main(void *ign)
{
	while (1) {
		int *p = global_ptr;
		if (p) {
			p = global_ptr;
			*p = 5;
		}
		STOP_ANALYSIS();
	}
	return NULL;
}

int
main()
{
	pthread_t thr;
	pthread_create(&thr, NULL, thr_main, NULL);

	time_t start_time = time(NULL);

	int t;
	while (time(NULL) < start_time + 10) {
		STOP_ANALYSIS();
		global_ptr = &t;
		STOP_ANALYSIS();

		usleep(1000000);

		STOP_ANALYSIS();
		global_ptr = NULL;
		STOP_ANALYSIS();
	}

	return 0;
}
