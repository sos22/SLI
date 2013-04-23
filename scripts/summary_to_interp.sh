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

${topdir}/ec_driver ${bin} ${bin}.tc ${bin}.bcg ${bin}.db ${output}.ced ${canon}
read ced_line < ${output}.ced
if [ "$ced_line" = "<empty>" ]
then
    exit 0
fi

${topdir}/ctoc_driver ${bin} ${output}.ced ${bin}.tc ${bin}.bcg ${bin}.db ${output}.cep.c

gcc -g -Wall -ldl -I ${topdir}/sli/enforce_crash -shared ${topdir}/cep_interpreter.o -x c ${output}.cep.c -o ${output}.interp.so
