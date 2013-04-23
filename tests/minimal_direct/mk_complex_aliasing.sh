#! /bin/bash

set -e

nr_stores="$1"
nr_loads="$2"

cat <<EOF
#include <pthread.h>
#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

#define NR_SLOTS 1000
static volatile int slots[NR_SLOTS];

#define STOP_ANALYSIS()					\
	asm (".fill 1000,1,0x90\n")
static volatile int
global;
static volatile bool
force_quit;

static void *
thr_main(void *ign)
{
EOF
for i in `seq 1 $nr_stores`
do
    echo "        unsigned long store_idx$i;"
done
for i in `seq 1 $nr_loads`
do
    echo "        unsigned long load_idx$i;"
done
cat <<EOF

	while (!force_quit) {
EOF
for i in `seq 1 $nr_stores`
do
    echo "                store_idx$i = random() % NR_SLOTS;"
done
for i in `seq 1 $nr_loads`
do
    echo "                load_idx$i = random() % NR_SLOTS;"
done
echo "                STOP_ANALYSIS();"
for i in `seq 1 $nr_stores`
do
    echo "                slots[store_idx${i}] = 1;"
done
echo -n "                assert("
for i in `seq 1 $nr_loads`
do
    if [ "$i" != 1 ]
    then
	echo -n " && "
    fi
    echo -n "slots[load_idx${i}] != 2"
done
echo ");"
cat <<EOF
                STOP_ANALYSIS();
        }
        return NULL;
}

volatile int confuse_compiler;

int
main()
{
	pthread_t thr;
	time_t start_time = time(NULL);
	int forever = 0;
        int i;
        int j;

        confuse_compiler = 1;
        j = confuse_compiler;
        STOP_ANALYSIS();

	pthread_create(&thr, NULL, thr_main, NULL);

	if (getenv("SOS22_RUN_FOREVER"))
		forever = 1;

        for (i = 0; i < NR_SLOTS; i++) {
                slots[i] = j;
        }

	while (forever || time(NULL) < start_time + 10) {
                sleep(1);
        }

	force_quit = true;
	pthread_join(thr, NULL);

	return 0;
}
EOF
