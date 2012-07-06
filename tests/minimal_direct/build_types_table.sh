#! /usr/bin/env bash

valgrind="../../../valgrind-ft-stage3/bin/valgrind"
program="$*"

# The test program contains racing bugs, or there wouldn't be any
# point in using it, so try running it three times before giving up.
for cntr in 1 2 3 4
do
    if [ "$cntr" = "4" ]
    then
	echo "Cannot run $*!"
	exit 1
    fi
    script -c "$valgrind --tool=ft2 $program" my_script && break
done
path=$(grep "^Dumping results to" my_script | sed 's,Dumping results to \(/tmp/types[0-9]*\.dat\).,\1,')
mv $path ${1}.types
rm -f my_script
