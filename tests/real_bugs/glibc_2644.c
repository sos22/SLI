/* Harness to try to trigger glibc bug 2644. */
#include <pthread.h>
#include <stdio.h>

static pthread_barrier_t barrier;

void *
thread_func(void *ignore)
{
	pthread_barrier_wait(&barrier);
	pthread_exit(NULL);
	printf("Zombied\n");
}

int
main()
{
	pthread_t thr;

	pthread_barrier_init(&barrier, NULL, 2);

	pthread_create(&thr, NULL, thread_func, NULL);

	pthread_barrier_wait(&barrier);

	pthread_exit(NULL);
	printf("Huh?\n");

	return 1;
}
