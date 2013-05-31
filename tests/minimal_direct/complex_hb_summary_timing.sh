#! /bin/bash

set -e
set -x

function tp() {
    local nr_accs="$1"
    echo -n "md_test_dir/complex_hb:nr_accs=${nr_accs}"
}
function mem_usage() {
    sed 's/^[0-9.]*: high water: \([0-9]*\), \([0-9]*\)$/\1 \2 + p/p;d' "$1" | dc
}

max_nr_accs=5
acc_step=2 # Must be even
nr_reps=1
discards=0

# Build everything we need before we start.
cat > extra_config2.h <<EOF
#define CONFIG_CLUSTER_THRESHOLD 500
#define CONFIG_TIMEOUT1 300
#define CONFIG_TIMEOUT2 300
EOF
if ! cmp -s extra_config.h extra_config2.h
then
    mv extra_config2.h extra_config.h
fi
make OPTIMIZE=y -j8 minimal_direct static canonicalise_types_table
for nr_acs in `seq 3 ${acc_step} ${max_nr_accs}`
do
    t=$(tp $nr_acs)
    if ! [ -f ${t}.c ] || [ tests/minimal_direct/mk_complex_hb.sh -nt ${t}.c ]
    then
	./tests/minimal_direct/mk_complex_hb.sh ${nr_acs} > "${t}.c"
    fi
    make OPTIMIZE=y ${t}.{exe,types,bcg}
    to_build="${to_build} ${t}.types.canon ${t}.db"
done
make -j8 OPTIMIZE=y ${to_build}

logfile=complex_hb_results
summarylog=gen_summaries
: > $summarylog
: > $logfile
for rep in `seq 1 $(($nr_reps + $discards))`
do
    schedule=$(mktemp)
    seq 3 $acc_step $max_nr_accs | ./scripts/shuffle.py > "$schedule"
    cntr=0
    max_cntr=$(wc -l ${schedule} | cut -f 1 -d' ')
    echo -n "Rep $rep of $(($nr_reps + $discards)), date = " >> $logfile
    date >> $logfile
    start_rep=$(date +%s)
    cat ${schedule} | while read nr_accs
    do
	now=$(date +%s)
	elapsed=$(($now - $start_rep))
	echo "Item ${cntr}/${max_cntr}, repetition ${rep}/$(($nr_reps + $discards)), in ${elapsed} seconds"
	# 100 is a guess for the average time each iter takes, from previous experiments.
	python -c "print '%dm%ds left' % (int((${elapsed}.0+100) * ($max_cntr - $cntr) / (($cntr+1.0) * 60.0)), int((${elapsed}.0+100)  * ($max_cntr - $cntr) / ($cntr+1.0)) % 60)"

	cntr=$(($cntr + 1))

	t=$(tp $nr_accs)
	rm -f bubble_data.log
	rm -f bubble_data2.log
	rm -rf logs crash_summaries
	mkdir logs crash_summaries

	./minimal_direct ${t}.{exe,types.canon,bcg,db} assertions
	# And check that it produced the expected set of summaries
   	# (i.e. none at all for easy mode, one for hard)
	if [ -r "crash_summaries/0" ]
	then
	    echo "${t} produced a summary (rep ${rep})?"
	    echo "$nr_accs $rep" >> ${summarylog}
	    ls crash_summaries >> ${summarylog}
	fi
	# Discard first sample to reduce risk of outliers.
	if [ $rep -le $discards ]
	then
	    continue
	fi
	if grep -q "out of memory" bubble_data.log bubble_data2.log
	then
	    echo "$nr_accs OOM" >> $logfile
	    continue
	fi
	if grep -q "timeout" bubble_data.log bubble_data2.log
	then
	    echo "$nr_accs timeout" >> $logfile
	    continue
	fi
	    
	hw=$(mem_usage bubble_data.log)
	mem_usage bubble_data2.log | while read hw2
	do
	    if [ $hw2 -gt $hw ]
	    then
		hw=$hw2
	    fi
	done
	start_time=$(grep "start crashing thread" bubble_data.log | sed 's/^\([0-9.]*\): .*/\1/')
	stop_time=$(grep "finish crashing thread" bubble_data.log | sed 's/^\([0-9.]*\): .*/\1/')
	time=$(python -c "print $stop_time - $start_time")
	echo "$nr_accs $hw $time" >> $logfile
    done
done

