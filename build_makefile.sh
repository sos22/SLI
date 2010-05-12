#! /bin/bash

set -e

input="$1"
output="$2"

input_base=$(dirname "$input")
defvars() {
    true
}
rules() {
    true
}
. "./$input"

for subdir in $subdirs
do
    echo "include ${input_base}/${subdir}/Makefile.mk"
done

for extra_mk in $extra_mks
do
    echo "include ${input_base}/${extra_mk}"
    echo "all_makefiles+=${input_base}/${extra_mk}"
done

for target in $targets
do
    echo "TARGETS+=$target"
done

echo "all_makefiles+=${output}"

defvars
rules
