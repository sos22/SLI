#! /bin/sh

set -e

make $1

t=../$1
shift
args="$*"

rm -rf res
mkdir res
cd res

objdump -d "$t" > disassembly

# First, collect a types table
../../valgrind-ft-stage3/bin/valgrind --tool=ft2 $t $args

# And a BCG table
../../valgrind-ft-stage3/bin/valgrind --tool=bcg $t $args

echo Done BCG

# Now run minimal_direct to build the crash summaries
mkdir crash_summaries
mkdir logs
../minimal_direct $t types1.dat callgraph1.dat

# Classify the logs
cd logs
for x in *
do
    ../../scripts/classify_split_typescript.sh $x
done
cd results
summarise_directory.sh

cd ../../
../enforce_crash $t types1.dat callgraph1.dat new_patch.so crash_summaries/*
