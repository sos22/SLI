#! /usr/bin/env bash

valgrind="/local/scratch/sos22/valgrind-ft-stage3/bin/valgrind"
program="$*"
typedb="${1/.exe/.types}"

# The test program contains racing bugs, or there wouldn't be any
# point in using it, so try running it three times before giving up.
for cntr in 1 2 3 4
do
    if [ "$cntr" = "4" ]
    then
	echo "Cannot run $*!"
	exit 1
    fi
    rm -f "$typedb"
    $valgrind --tool=ft2 --output="$typedb" "$program" && break
done
