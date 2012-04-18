#! /bin/sh

start="$1"
end="$2"

cd /local/scratch/sos22/sli/2012-04-04b
./minimal_direct ./mysqld types-new-format-no-head-canon.dat callgraph-newformat.dat ${start}...${end}