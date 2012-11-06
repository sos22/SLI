#! /usr/bin/env bash

valgrind="/local/scratch/sos22/valgrind-ft-stage3/bin/valgrind"
program="$*"

rm -f callgraph1.dat
for cntr in 1 2 3 4
do
    if [ "$cntr" = "4" ]
    then
	echo "Cannot run $*!"
	exit 1
    fi
    $valgrind --tool=bcg $program && break
done
mv callgraph1.dat ${1/.exe/.bcg}
