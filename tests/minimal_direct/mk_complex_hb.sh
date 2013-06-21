#! /bin/bash

set -e
set -x

nr_edges="$1"

cat <<EOF
#include <pthread.h>
#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

#define STOP_ANALYSIS()					\
	asm (".fill 1000,1,0x90\n")
static volatile int
global;
static volatile bool
force_quit;

static void
worker(void)
{
EOF
nr_vars=$(( $((nr_edges / 2)) ))
for i in `seq 0 $nr_vars`
do
    echo "        int x$i;"
done
echo "        STOP_ANALYSIS();"
for i in `seq 0 $nr_vars`
do
    echo "        x$i = global;"
done
echo -n "        assert(!("
for i in `seq 0 $nr_vars`
do
    if [ "$i" != 0 ]
    then
	echo -n " && "
    fi
    echo -n "x$i == $i"
done
echo "));"
cat <<EOF
        STOP_ANALYSIS();
}
static void worker(void) __attribute__((noinline));

static void *
thr_main(void *ign)
{
	while (!force_quit) {
                worker();
        }
        return NULL;
}

int
main()
{
	pthread_t thr;
	time_t start_time = time(NULL);
	int forever = 0;

	pthread_create(&thr, NULL, thr_main, NULL);

	if (getenv("SOS22_RUN_FOREVER"))
		forever = 1;

	while (forever || time(NULL) < start_time + 60) {
		STOP_ANALYSIS();
EOF
for i in `seq 0 $nr_vars`
do
    echo "                global = $i;"
done
cat <<EOF
		STOP_ANALYSIS();
	}

	force_quit = true;
	pthread_join(thr, NULL);

	return 0;
}
EOF