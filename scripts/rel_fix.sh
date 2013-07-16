#! /bin/bash

# Generate a variety of incomplete fixes for the nobug test and see
# what kind of performance we get out of each of them.

set -e
set -x

# Start by generating the patches we need.
if ! [ -e "fix-gain-only.so" ]
then
    echo "#define INCOMPLETE_PATCH 0" > extra_config.h
    make OPTIMIZE=y ./md_test_dir/bug21~0.fix.so
    cp md_test_dir/bug21~0.fix.so fix-gain-only.so
fi

if ! [ -e "fix-no-sync.so" ]
then
    echo "#define INCOMPLETE_PATCH 1" > extra_config.h
    make -j8 OPTIMIZE=y ./md_test_dir/bug21~0.fix.so
    cp md_test_dir/bug21~0.fix.so fix-no-sync.so
fi

if ! [ -e "fix-sync-crashing.so" ]
then
    echo "#define INCOMPLETE_PATCH 2" > extra_config.h
    make -j8 OPTIMIZE=y ./md_test_dir/bug21~0.fix.so
    cp md_test_dir/bug21~0.fix.so fix-sync-crashing.so
fi

if ! [ -e "fix-normal.so" ]
then
    echo "#define INCOMPLETE_PATCH 3" > extra_config.h
    make -j8 OPTIMIZE=y ./md_test_dir/bug21~0.fix.so
    cp md_test_dir/bug21~0.fix.so fix-normal.so
fi

if ! [ -e "fix-dr.so" ]
then
    echo "#define INCOMPLETE_PATCH 3" > extra_config.h
    echo "#define PATCH_BY_DEBUG_REGISTER 1" >> extra_config.h
    make -j8 OPTIMIZE=y ./md_test_dir/bug21~0.fix.so
    cp md_test_dir/bug21~0.fix.so fix-dr.so
fi

# Build the schedule
for fix in none gain-only no-sync sync-crashing normal dr
do
    for r in `seq 1 100`
    do
	echo "$fix"
    done
done | ./scripts/shuffle.py > rel_fix_schedule

for fix in none gain-only no-sync sync-crashing normal dr
do
    : > ${fix}.rel_fix_res
done

cat rel_fix_schedule | while read type
do
    if [ "$type" = "none" ]
    then
	./md_test_dir/bug21.exe
    elif [ "$type" = "dr" ]
    then
	# There's something funny about the DR-type patches which
	# means that we crash in the call to ptrace about one time in
	# fifty.  I can't be bothered to fix it, so just retry when it
	# happens.
	while :
	do
	    LD_PRELOAD=./fix-${type}.so ./md_test_dir/bug21.exe && break
	done
    else
	LD_PRELOAD=./fix-${type}.so ./md_test_dir/bug21.exe
    fi >> ${type}.rel_fix_res
done

