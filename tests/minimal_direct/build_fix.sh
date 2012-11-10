#! /bin/sh

bugname="$1"

set -e

rm -f "${bugname}.fix.c" "${bugname}.fix.so"
make "${bugname}.fix.so"
