#! /bin/bash

binary="$1"
# Canonicalised types table
types="$2"
callgraph="$3"
# The machines directory generated by minimal_direct when
# CONFIG_RECORD_MACHINE_OPTIMISATIONS is set.
dir=$(canon $4)
# Where to put our results
res=$(canon $5)

echo $dir

scratch=$(canon scratch)

set -e
if [ ! -d ${res} ]
then
    mkdir ${res}
    mkdir ${res}/trivial
    mkdir ${res}/pass
    mkdir ${res}/fail

    mkdir ${scratch}
    pushd ${scratch}
    for x in ${dir}/*
    do
	ln -s $x
    done
    popd
fi

for x in ${scratch}/*
do
    id=$(basename $x)
    script -f -c "../scripts/cross_check_machine.sh $binary $types $callgraph $x" logfile
    if grep -q "Trivial machine" logfile
    then
	touch res/trivial/$id
    elif grep -q "Result: passed" logfile
    then
	mv logfile res/pass/$id
    else
	mv logfile res/fail/$id
    fi
    rm $x
done