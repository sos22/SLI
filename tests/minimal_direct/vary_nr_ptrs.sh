#! /bin/bash

set -e
set -x

nr_reps=110
nr_discards=0

function abscissae() {
    echo 1 2 3 4 5 6 7 8 9 10 20 30 40 50 60 70 80 90 100 150 200 250 300 350 400 450 500 750 1000 2000 3000 4000 5000 7500 10000 20000 40000 80000 160000 320000
}
function tp() {
    local n="$1"
    echo "md_test_dir/indexed_toctou:nr_ptrs=$1"
}

# Build the bits we need.

cat > extra_config2.h <<EOF
#define CONFIG_CLUSTER_THRESHOLD 20
#define CONFIG_TIMEOUT1 300
#define CONFIG_TIMEOUT2 300
EOF
if ! cmp -s extra_config.h extra_config2.h
then
    mv extra_config2.h extra_config.h
fi

# Stuff which can't be parallelised
to_build1=""
# Stuff which can be
to_build2=""
for i in `abscissae`
do
    p=$(tp $i)
    if ! [ -f ${p}.exe ] || [ tests/minimal_direct/bug2.c -nt ${p}.exe ]
    then
	gcc -Wall -g -O -pthread tests/minimal_direct/bug2.c -DNR_PTRS=$i -o ${p}.exe
    fi
    to_build1="$to_build1 ${p}.bcg ${p}.types"
    to_build2="$to_build2 ${p}~0.interp.so"
done
make OPTIMIZE=y $to_build1
make OPTIMIZE=y $to_build2

for i in `abscissae`
do
    # Surprise!  You can't LD_PRELOAD anything with a colon in the
    # filename, because ld.so treats it as a separator.  Rename them.
    p=$(tp $i)
    old_name=${p}~0.interp.so
    new_name=$(echo ${p}~0.interp.so | sed 's/[:=]/~/g')
    rm -f "$new_name"
    ln -s $(basename $old_name) "$new_name"
done

logfile=vary_nr_ptrs
: > $logfile
sched=$(mktemp)
for i in `seq 1 $(($nr_reps + $nr_discards))`
do
    for a in `abscissae`
    do
	echo with $a
	if [ "$a" -lt 4000 ]
	then
	    echo without $a
	fi
    done
done | ./scripts/shuffle.py > "$sched"

cat "$sched" | while read use_interp absc
do
    p=$(tp $absc)
    t=$(mktemp)
    interp=$(echo ${p}~0.interp.so | sed 's/[:=]/~/g')
    if [ "$use_interp" = "with" ]
    then
	! SOS22_ENFORCER_RANDOMISE=1 SOS22_RUN_FOREVER=1 LD_PRELOAD=${interp} ./scripts/sane_time "$t" ${p}.exe
    else
	! SOS22_RUN_FOREVER=1 ./scripts/sane_time "$t" ${p}.exe
    fi
    read time < "$t"
    rm -f "$t"
    echo "$use_interp $absc $time" >> "$logfile"
done