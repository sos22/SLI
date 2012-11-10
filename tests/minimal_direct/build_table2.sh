#! /bin/bash


cat >&3 <<EOF
\begin{tabular}{lllll}
Test name & No enforcer & No side-condition checking & Full enforcer & DataCollider \\\\
\hline
EOF

_make() {
    echo "make $*" >&2
}

get_dist() {
    _make md_test_dir/"$1".crash_times_dist
    sed 's/\\/\\\\/g' md_test_dir/$1.crash_times_dist
}

cat tests/minimal_direct/bug_table.txt | while read exe_name exe_desc nr_bugs
do
    exe_descr=$(echo $exe_desc | tr '~' ' ')
    ctd=$(get_dist ${exe_name})
    dcctd=$(get_dist ${exe_name}.dc)
    printf "\hline{}%-20s & %-20s & " "$exe_descr" "$ctd" >&3
    if [ "$nr_bugs" = 1 ]
    then
	esctd=$(get_dist ${exe_name}~0.S)
	ectd=$(get_dist ${exe_name}~0)
	printf "%-20s & %-20s & %-20s \\\\\\\\\n" "$esctd" "$ectd" "$dcctd" >&3
    else
	printf "                     &                       & %-20s\\\\\\\\\n" "$dcctd" >&3
	for i in `seq 0 $(($nr_bugs - 1))`
	do
	    esctd=$(get_dist ${exe_name}~${i}.S)
	    ectd=$(get_dist ${exe_name}~${i})
	    printf " & & %-20s & %-20s & \\\\\\\\\n" "$esctd" "$ectd" >&3
	done
    fi
done

echo "\end{tabular}" >&3
