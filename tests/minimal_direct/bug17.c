/* A bug which doesn't work if you have W isolation turned on. */
#include <assert.h>
#include <stdlib.h>
#include <pthread.h>
#include <unistd.h>

#include "test.h"

#define NR_ATTEMPTS 100

struct the_struct {
	struct the_struct *chain;
	volatile int v;
};
static struct the_struct *volatile
global_ptr;

static pthread_barrier_t
the_barrier;

static void *
thr_main(void *ign)
{
	struct the_struct *chain_start;
	int i;

	while (1) {
		struct the_struct *s;

		chain_start = NULL;
		global_ptr = NULL;

		pthread_barrier_wait(&the_barrier);

		for (i = 0; i < NR_ATTEMPTS; i++) {
			s = malloc(sizeof(struct the_struct));
			s->chain = chain_start;
			chain_start = s;
			s->v = 7;
			global_ptr = s;
			assert(s->v == 7);
		}

		pthread_barrier_wait(&the_barrier);
		while (chain_start) {
			s = chain_start->chain;
			free(chain_start);
			chain_start = s;
		}
		pthread_barrier_wait(&the_barrier);
	}
}

int
main()
{
	pthread_t thr;
	time_t start_time = time(NULL);
	int forever = 0;
	int i;

	pthread_barrier_init(&the_barrier, NULL, 2);
	pthread_create(&thr, NULL, thr_main, NULL);

	if (getenv("SOS22_RUN_FOREVER")) {
		forever = 1;
	}

	while (forever || time(NULL) < start_time + 10) {
		struct the_struct *p;

		pthread_barrier_wait(&the_barrier);

		for (i = 0; i < NR_ATTEMPTS; i++) {
			p = global_ptr;
			if (p) {
				p->v = 5;
			}
		}

		pthread_barrier_wait(&the_barrier);
		pthread_barrier_wait(&the_barrier);
	}

	return 0;

}

