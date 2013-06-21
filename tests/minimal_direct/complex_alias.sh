#! /bin/bash

set -e
set -x

function tp() {
    local nr_loads="$1"
    local nr_stores="$2"
    local easy_version="$3"
    echo -n "md_test_dir/complex_alias:nr_loads=${nr_loads};nr_stores=${nr_stores};easy=${easy_version}"
}

if [ "$1" = "easy" ]
then
    max_loads=286
    lstep=5
    function max_stores() {
	local nr_loads="$1"
	if [ "$nr_loads" -le 6 ]
	then
	    echo 166
	elif [ "$nr_loads" -le 11 ]
	then
	    echo 106
	elif [ "$nr_loads" -le 16 ]
	then
	    echo 86
	elif [ "$nr_loads" -le 21 ]
	then
	    echo 76
	elif [ "$nr_loads" -le 26 ]
	then
	    echo 71
	elif [ "$nr_loads" -le 31 ]
	then
	    echo 66
	elif [ "$nr_loads" -le 36 ]
	then
	    echo 61
	elif [ "$nr_loads" -le 41 ]
	then
	    echo 56
	elif [ "$nr_loads" -le 46 ]
	then
	    echo 51
	elif [ "$nr_loads" -le 56 ]
	then
	    echo 46
	elif [ "$nr_loads" -le 66 ]
	then
	    echo 41
	elif [ "$nr_loads" -le 76 ]
	then
	    echo 36
	elif [ "$nr_loads" -le 91 ]
	then
	    echo 31
	elif [ "$nr_loads" -le 111 ]
	then
	    echo 26
	elif [ "$nr_loads" -le 141 ]
	then
	    echo 21
	elif [ "$nr_loads" -le 196 ]
	then
	    echo 16
	else
	    echo 11
	fi
    }
    sstep=5
    easy_version=y
else
    max_loads=12
    lstep=1
    function max_stores() {
	local nr_loads="$1"
	if [ "$nr_loads" -le 2 ]
	then
	    echo 159
	elif [ "$nr_loads" = 3 ]
	then
	    echo 74
	elif [ "$nr_loads" = 4 ]
	then
	    echo 27
	elif [ "$nr_loads" = 5 ]
	then
	    echo 14
	elif [ "$nr_loads" = 6 ]
	then
	    echo 4
	elif [ "$nr_loads" = 7 ]
	then
	    echo 3
	else
	    echo 2
	fi
    }
    sstep=1
    easy_version=n
fi

nr_reps=11
discards=0

cat > extra_config2.h <<EOF
#define CONFIG_CLUSTER_THRESHOLD 500
#define CONFIG_TIMEOUT1 300
#define CONFIG_TIMEOUT2 300
#define CONFIG_NO_SELF_RACE 1
EOF
if ! cmp -s extra_config.h extra_config2.h
then
    mv extra_config2.h extra_config.h
fi

make OPTIMIZE=y -j8 minimal_direct static canonicalise_types_table
to_build=""
for nr_loads in `seq 1 ${lstep} ${max_loads}`
do
    for nr_stores in `seq 1 ${sstep} $(($(max_stores $nr_loads) + ${sstep} - 1))`
    do
	# Make sure that all of the needed files have been generated
	# before we start
	t=$(tp $nr_loads $nr_stores $easy_version)
	if ! [ -f ${t}.c ] || [ tests/minimal_direct/mk_complex_aliasing.sh -nt ${t}.c ]
	then
	    ./tests/minimal_direct/mk_complex_aliasing.sh ${nr_stores} ${nr_loads} ${easy_version} > "${t}.c"
	fi
	make OPTIMIZE=y ${t}.{exe,types,bcg}
	to_build="${to_build} ${t}.types.canon ${t}.db"
    done
done
make -j8 OPTIMIZE=y ${to_build}

function mem_usage() {
    sed 's/^[0-9.]*: high water: \([0-9]*\), \([0-9]*\)$/\1 \2 + p/p;d' "$1" | dc
}

logfile=complex_alias_results
summarylog=gen_summaries
: > $summarylog
: > $logfile
for rep in `seq 1 $(($nr_reps + $discards))`
do
    schedule=$(mktemp)
    for nr_loads in `seq 1 ${lstep} ${max_loads}`
    do
	for nr_stores in `seq 1 ${sstep} $(max_stores $nr_loads)`
	do
	    echo $nr_loads $nr_stores
	done
    done | ./scripts/shuffle.py > ${schedule}
    cntr=0
    max_cntr=$(wc -l ${schedule} | cut -f 1 -d' ')
    echo -n "Rep $rep of $(($nr_reps + $discards)), date = " >> $logfile
    date >> $logfile
    start_rep=$(date +%s)
    cat ${schedule} | while read nr_loads nr_stores
    do
	now=$(date +%s)
	elapsed=$(($now - $start_rep))
	echo "Item ${cntr}/${max_cntr}, repetition ${rep}/$(($nr_reps + $discards)), in ${elapsed} seconds"
	# 87 is a guess for the average time each iter takes, from previous experiments.
	python -c "print '%dm%ds left' % (int((${elapsed}.0+87) * ($max_cntr - $cntr) / (($cntr+1.0) * 60.0)), int((${elapsed}.0+87)  * ($max_cntr - $cntr) / ($cntr+1.0)) % 60)"

	cntr=$(($cntr + 1))

	t=$(tp $nr_loads $nr_stores $easy_version)
	rm -f bubble_data.log
	rm -f bubble_data2.log
	rm -rf logs crash_summaries
	mkdir logs crash_summaries

	./minimal_direct ${t}.{exe,types.canon,bcg,db} assertions
	# And check that it produced the expected set of summaries
   	# (i.e. none at all for easy mode, one for hard)
	if [ "$easy_version" = "y" ]
	then
	    if [ -r "crash_summaries/0" ]
	    then
		echo "${t} produced a summary (rep ${rep})?"
		echo "$nr_loads $nr_stores $rep" >> ${summarylog}
		continue
	    fi
	else
	    if ! [ -r "crash_summaries/0" ] || [ -r "crash_summaries/1" ]
	    then
		echo "${t} produced $(ls crash_summaries | wc -l) summaries (rep ${rep})?"
		echo "$nr_loads $nr_stores $rep" >> ${summarylog}
	    fi
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

