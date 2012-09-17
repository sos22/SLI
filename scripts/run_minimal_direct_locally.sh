#! /bin/sh

jobid="$1"
tag="$2"
start="$3"
end="$4"

set -e
set -x

ulimit -c unlimited

echo "Arguments $*"
cd /local/scratch/sos22/sli/${tag}
mkdir ${jobid}
cd ${jobid}
ln -s ../static.db
mkdir logs
mkdir crash_summaries
../../minimal_direct ../mysqld ../types-new-format-no-head-canon.dat ../callgraph-newformat.dat ${start}...${end}
