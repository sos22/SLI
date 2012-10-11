#include <pthread.h>
#include <stdbool.h>
#include <stdio.h>
#include <unistd.h>

static int *volatile global_ptr;

static long read_events;
static long write_events;
static volatile bool force_quit;

#define BAD_PTR ((void *)0x57ul)
#define STOP_ANALYSIS()					\
	asm (".fill 100,1,0x90\n")

static void *
thr_main(void *ign)
{
	static int q;
	while (!force_quit) {
		STOP_ANALYSIS();
		global_ptr = &q;
		*global_ptr = 6;
		STOP_ANALYSIS();
		read_events++;
	}
	return NULL;
}

int
main()
{
	pthread_t thr;

	pthread_create(&thr, NULL, thr_main, NULL);

	usleep(100000);
	time_t start_time = time(NULL);

	while (time(NULL) < start_time + 100) {
		STOP_ANALYSIS();
		global_ptr = BAD_PTR;
		STOP_ANALYSIS();
		write_events++;
	}

	printf("%ld read events, %ld write\n", read_events, write_events);
	return 0;
}