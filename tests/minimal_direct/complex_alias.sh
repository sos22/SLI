#! /bin/bash

set -e
set -x

function tp() {
    local nr_loads="$1"
    local nr_stores="$2"
    echo -n "md_test_dir/complex_alias:nr_loads=${nr_loads};nr_stores=${nr_stores};max_loads=${max_loads};max_stores=${max_stores}"
}

max_loads=100
max_stores=100
nr_reps=1
discards=0

cat > extra_config.h <<EOF
#define CONFIG_CLUSTER_THRESHOLD 500
#define CONFIG_TIMEOUT1 300
#define CONFIG_TIMEOUT2 300
EOF
make OPTIMIZE=y minimal_direct static canonicalise_types_table
for nr_loads in `seq 1 ${max_loads}`
do
    for nr_stores in `seq 1 ${max_stores}`
    do
	# Make sure that all of the needed files have been generated
	# before we start
	t=$(tp $nr_loads $nr_stores)
	if ! [ -f ${t}.c ] || [ tests/minimal_direct/mk_complex_aliasing.sh -nt ${t}.c ]
	then
	    ./tests/minimal_direct/mk_complex_aliasing.sh ${max_stores} ${max_loads} ${nr_stores} ${nr_loads} > "${t}.c"
	fi
	make OPTIMIZE=y ${t}.{exe,bcg,types.canon,db}
    done
done

function mem_usage() {
    sed 's/^[0-9.]*: high water: \([0-9]*\), \([0-9]*\)$/\1 \2 + p/p;d' "$1" | dc
}

logfile=complex_alias_results
: > $logfile
for rep in `seq 1 $(($nr_reps + $discards))`
do
    schedule=$(mktemp)
    for nr_loads in `seq 1 ${max_loads}`
    do
	for nr_stores in `seq 1 ${max_stores}`
	do
	    echo $nr_loads $nr_stores
	done
    done | ./scripts/shuffle.py > ${schedule}
    cat ${schedule} | while read nr_loads nr_stores
    do
	t=$(tp $nr_loads $nr_stores)
	rm -f bubble_data.log
	rm -f bubble_data2.log
	rm -rf logs crash_summaries
	mkdir logs crash_summaries

	./minimal_direct ${t}.{exe,types.canon,bcg,db} assertions
	# And check that it produced the expected set of summaries
   	# (i.e. none at all)
	if [ -r "crash_summaries/0" ]
	then
	    echo "${t} produced a summary (rep ${rep})?"
	    exit 1
	fi
	# Discard first sample to reduce risk of outliers.
	if [ $rep -le $discards ]
	then
	    continue
	fi
	if grep -q "out of memory" bubble_data.log bubble_data2.log
	then
	    echo "$nr_loads $nr_stores OOM" >> $logfile
	    continue
	fi
	if grep -q "timeout" bubble_data.log bubble_data2.log
	then
	    echo "$nr_loads $nr_stores timeout" >> $logfile
	    continue
	fi
	    
	hw1=$(mem_usage bubble_data.log)
	hw2=$(mem_usage bubble_data2.log)
	if [ $hw1 -gt $hw2 ]
	then
	    hw=$hw1
	else
	    hw=$hw2
	fi
	start_time=$(grep "start crashing thread" bubble_data.log | sed 's/^\([0-9.]*\): .*/\1/')
	stop_time=$(grep "finish crashing thread" bubble_data.log | sed 's/^\([0-9.]*\): .*/\1/')
	time=$(python -c "print $stop_time - $start_time")
	echo "$nr_loads $nr_stores $hw $time" >> $logfile
    done
done

