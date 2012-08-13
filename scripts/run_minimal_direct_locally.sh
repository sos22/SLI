#! /bin/sh

start="$1"
end="$2"

set -e
set -x

ulimit -c unlimited

cd /local/scratch/sos22/sli/2012-08-12
../minimal_direct ./mysqld types-new-format-no-head-canon.dat callgraph-newformat.dat ${start}...${end}
