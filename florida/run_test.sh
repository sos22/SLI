#! /bin/bash

summary=$1

mkdir -p enforcers
mv enforce_crash_* enforcers

echo "Considering summary $summary..."
if ! ../enforce_crash mysqld types1.dat callgraph1.dat out.elf $summary 
then
    echo "enforce_crash returned an error."
    exit 0
fi

start_pwd=${PWD}

try_stall_setting () {
    echo "Trying summary ${summary}, max stalls $1"
    export SOS22_ENFORCER_MAX_STALLS="$1"
    cd /local/scratch/sos22/mysql-5.5.6-rc/mysql-test
    ./mtr --testcase-timeout=99999 --max-test-fail=1 rpl_change_master
    echo "Core files:"
    find var -name '*core*'

    echo -n "Results for summary ${summary}, max stalls ${SOS22_ENFORCER_MAX_STALLS}: "
    if [ $(find var -name '*core*' | wc -l) == 0 ]
    then
	echo "No cores"
    else
	echo "Found core files"
	coredir=${start_pwd}/run_test_cores_${summary#crash_summaries/}-${SOS22_ENFORCER_MAX_STALLS}
	mkdir -p ${coredir}
	cp out.elf ${coredir}
	find var -name '*core*' | xargs cp -t ${coredir}
	cd ${start_pwd}
	cp enforce_crash_* ${coredir}
	cp out.elf ${coredir}
	echo "Stashed in ${coredir}"
    fi
}

try_stall_setting 10000
try_stall_setting 4000
try_stall_setting 1000
try_stall_setting 10000
try_stall_setting 4000
try_stall_setting 1000
try_stall_setting 1000