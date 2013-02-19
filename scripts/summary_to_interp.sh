#! /bin/sh

set -e

bin=$1
summary=$2

topdir=/local/scratch/sos22/sli

${topdir}/canonicalise_crash_summary0 $summary $summary.canon0
${topdir}/canonicalise_crash_summary2 $summary.canon0 $summary.canon2
${topdir}/canonicalise_crash_summary0 $summary.canon2 $summary.canon4

${topdir}/enforce_crash ${bin} ${bin}.tc ${bin}.bcg ${bin}.db ${summary}.ced ${summary}.canon4

${topdir}/ced_to_cep ${bin} ${summary}.ced ${bin}.tc ${bin}.bcg ${bin}.db ${summary}.cep.c

gcc -Wall -ldl -I ${topdir}/sli/enforce_crash -shared ${topdir}/cep_interpreter.o -x c ${summary}.cep.c -o ${summary}.interp.so
