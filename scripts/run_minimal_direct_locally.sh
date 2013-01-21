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
mkdir logs
mkdir crash_summaries
SOS22_MINIMAL_DIRECT_TIMEOUT=60 SOS22_MINIMAL_DIRECT_INSTR_SCHEDULE=../../reduced_schedule ../../../minimal_direct ../../mysqld ../../types.dat.canon ../../callgraph1.dat ../../static.db ${start}...${end}
