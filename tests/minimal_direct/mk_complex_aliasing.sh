#! /bin/bash

set -e

wild_stores="$1"
wild_loads="$2"
easy_version="$3"

cat <<EOF
#include <pthread.h>
#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

#define NR_SLOTS 100
static volatile unsigned long slots[NR_SLOTS];

#define STOP_ANALYSIS()					\
	asm (".fill 10000,1,0x90\n")

static volatile int
global;
static volatile bool
force_quit;

static void *
thr_main(void *ign)
{
EOF
for i in `seq 1 $wild_stores`
do
    echo "        volatile unsigned long store_idx$i;"
done
for i in `seq 1 $wild_loads`
do
    echo "        volatile unsigned long load_idx$i;"
done
cat <<EOF

	while (!force_quit) {
EOF
for i in `seq 1 $wild_stores`
do
    echo "                store_idx$i = random() % NR_SLOTS;"
done
for i in `seq 1 $wild_loads`
do
    echo "                load_idx$i = random() % NR_SLOTS;"
done
echo "                STOP_ANALYSIS();"
for i in `seq 1 $wild_stores`
do
    if [ "$easy_version" = "y" ]
    then
	echo "                slots[store_idx${i}] = $i;"
    else
	echo "                slots[store_idx${i}] = ${i};"
    fi
done
if [ "$easy_version" = "n" ]
then
    echo -n "                assert(("
    for i in `seq 1 $wild_loads`
    do
	if [ "$i" != 1 ]
	then
	    echo -n " + "
	fi
	echo -n "slots[load_idx${i}]"
    done
    echo ") != ($wild_loads * ($wild_stores + 1) + 1));"
elif [ "$easy_version" = "y" ]
then
    echo -n "                assert("
    for i in `seq 1 $wild_loads`
    do
	if [ "$i" != 1 ]
	then
	    echo -n " && "
	fi
	echo -n "slots[load_idx${i}] != $(($wild_stores + 1 + $i))"
    done
    echo ");"
else
    echo "Final argument should be either y (for the easy version of the test) or n (for the hard version)" >&2
    exit 1
fi
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

	pthread_create(&thr, NULL, thr_main, NULL);

        i = random() % NR_SLOTS;
        STOP_ANALYSIS();
EOF
if [ "$easy_version" = "y" ]
then
    echo "        slots[i] = 0;"
else
    echo "        slots[i] = $wild_stores + 1;"
fi
cat <<EOF
        STOP_ANALYSIS();

	if (getenv("SOS22_RUN_FOREVER"))
		forever = 1;

	while (forever || time(NULL) < start_time + 2) {
                sleep(1);
        }

	force_quit = true;
	pthread_join(thr, NULL);

	return 0;
}
EOF
