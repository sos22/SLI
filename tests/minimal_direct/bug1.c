#include <pthread.h>
#include <stdio.h>
#include <time.h>
#include <unistd.h>

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
		int cntr;
		for (cntr = 0; cntr < 100; cntr++)
			asm ("nop");
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
		global_ptr = &t;
		int cntr;
		for (cntr = 0; cntr < 100; cntr++)
			asm ("nop");
		usleep(1000000);
		global_ptr = NULL;
		for (cntr = 0; cntr < 100; cntr++)
			asm ("nop");
	}

	return 0;
}
