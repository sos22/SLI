#! /bin/bash

if [ -e "ceds" ] || [ -e "logs" ]
then
    echo "ceds directory already exists"
    exit 1
fi

TOP=${0%test_patches.sh}

echo "topdir $TOP"

orig_pwd=${PWD}
${TOP}/get_status.sh

topdir=${PWD}

mkdir ceds
mkdir patches
mkdir logs
mkdir patch_sources
mkdir cores

rm enforce_crash_*
for crash_summary in crash_summaries/684 crash_summaries/*
do
    echo -n "Processing $crash_summary at "
    date +%s

    id=${crash_summary#crash_summaries/}
    ced=ceds/${id}.ced
    patch=patches/${id}.elf

    if [ -e "${ced}" ]
    then
	echo "Huh? Found CED $ced already existed?"
	exit 1
    fi

    echo -n "Start generating CED at "
    date +%s

    echo "crash summary $crash_summary"
    script -f -c "../enforce_crash mysqld types1.dat callgraph1.dat ${ced} ${crash_summary}" logs/enforce_crash${id}.scr || continue

    echo -n "Start generating patch at "
    date +%s

    script -f -c "../ced_to_patch mysqld ${ced} ${patch}" logs/ced_to_patch${id}.scr || continue
    mv enforce_crash_* patch_sources/${id}.c

    echo -n "Start testing patch ${patch} at "
    date +%s

    export SOS22_ENFORCER_MAX_STALLS=10000
    export SOS22_ENFORCER_PATH=${topdir}/${patch}
    cd /local/scratch/sos22/mysql-5.5.6-rc/mysql-test
    rm -rf var
    script -f -c "echo patch \$SOS22_ENFORCER_PATH; ./mtr --testcase-timeout=99999 --max-test-fail=1 rpl_change_master" ${topdir}/logs/mtr${id}.scr

    echo -n "Finished test harness at "
    date +%s

    echo "Core files:"
    find var -name '*core*'

    if [ "$(find var -name '*core*' | wc -l)" -eq 0 ]
    then
	echo "No cores"
    else
	echo "Found core files"
	coredir=${topdir}/cores/${id}
	mkdir ${coredir}
	find var -name '*core*' | nl | while read nr fname
	do
	    cp $fname ${coredir}/core.${nr}
	done
	echo "Stashed in ${coredir}"
    fi
    cd ${topdir}
done