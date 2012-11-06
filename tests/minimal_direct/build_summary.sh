#! /bin/bash

exe="$1"

set -e
set -x

rm -rf ${exe}.summaries
make "${exe}.summaries"
for x in "${exe}.summaries/*"
do
    i=$(basename $x)
    rm -f ${exe}~$i.summary{,.canon0,.canon2,.canon3,.canon4}
    make "${exe}~$i.summary.canon4"
done
