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
link() {
    local prog="$1"
    shift
    local objs="$*"
    cat <<EOF
ifeq (\$(VERBOSE),y)
${prog}: ${objs}
	gcc -lsqlite3 -lrt \$(PROFILE_FLAGS) -lgcc -lstdc++ -lm -Wl,-\( \$^ -Wl,-\) -o \$@
else
${prog}: ${objs}
	@printf "Link [%-43s]\\n" \$@ ; \\
	gcc -lsqlite3 -lrt \$(PROFILE_FLAGS) -lgcc -lstdc++ -lm -Wl,-\( \$^ -Wl,-\) -o \$@
endif
EOF
}
. "./$input"

echo "# Generated from ${input} by $0; do not edit"
echo
echo

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
