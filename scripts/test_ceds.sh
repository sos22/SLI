#! /bin/sh

TOP=${0%test_ceds.sh}

echo "topdir $TOP"

orig_pwd=${PWD}
${TOP}/get_status.sh

mkdir cores
mkdir logs
mkdir patches

for ced in ceds/684.ced ceds/*.ced
do
    echo -n "processing $ced at "
    date +%s

    id=${ced#ceds/}
    id=${id%.ced}
    patch=`pwd`/patches/${id}.elf

    rm enforce_crash_*
    if ! script -f -c "../ced_to_patch mysqld ${ced} ${patch}" logs/ced_to_patch${id}.scr
    then
	echo "Failed to generate patch $patch!"
	echo "Failed to generate patch $patch!" >> errorlog
	continue
    fi

    echo -n "start testing at "
    date +%s

    export SOS22_ENFORCER_MAX_STALLS=10000
    export SOS22_ENFORCER_PATH=${patch}
    cd /local/scratch/sos22/mysql-5.5.6-rc/mysql-test
    rm -rf var
    script -f -c "./mtr --testcase-timeout=99999 --max-test-fail=1 rpl_change_master" ${orig_pwd}/logs/mtr${id}.scr

    echo -n "Finished test harness at "
    date +%s

    echo "Core files:"
    find var -name '*core*'

    if [ "$(find var -name '*core*' | wc -l)" -eq 0 ]
    then
	echo "No cores"
    else
	echo "Found core files"
	coredir=${orig_pwd}/cores/${id}
	mkdir ${coredir}
	find var -name '*core*' | nl | while read nr fname
	do
	    cp $fname ${coredir}/core.${nr}
	done
	echo "Stashed in ${coredir}"
    fi
    cd ${orig_pwd}
done