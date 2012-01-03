#! /bin/bash

ulimit -c unlimited

export SOS22_ENFORCER_PATH=${PWD}/out.elf
echo "Enforcer is $SOS22_ENFORCER_PATH"

mkdir -p run_test_logs

for x in crash_summaries/*
do
    log=${x/crash_summaries/run_test_logs}
    if [ -e "$log" ]
    then
	echo "Huh? log file $log already exists"
	exit 1
    fi
    script -f -c "./run_test.sh $x" ${log}
done
