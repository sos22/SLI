#! /bin/sh

bugname="$1"

set -e

rm -f "${bugname}.cep.c" "${bugname}.ced" "${bugname}.interp.so"
make "${bugname}.interp.so"
