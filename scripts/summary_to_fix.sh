#! /bin/sh

set -e
set -x

bin=$1
shift
output=$1
shift
summaries=$*

topdir=/local/scratch/sos22/sli

canon=""
for summary in $summaries
do
    ${topdir}/canonicalise_crash_summary0 $summary $summary.canon0
    ${topdir}/canonicalise_crash_summary2 $summary.canon0 $summary.canon2
    ${topdir}/canonicalise_crash_summary0 $summary.canon2 $summary.canon4
    canon="$canon ${summary}.canon4"
done

${topdir}/s2f_driver ${bin} ${bin}.tc ${bin}.bcg ${bin}.db ${output}.fix.c ${canon}
gcc -g -shared -fPIC -I/local/scratch/sos22/sli/sli ${output}.fix.c -o ${output}.fix.so

