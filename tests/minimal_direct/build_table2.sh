#! /bin/bash


cat >&3 <<EOF
\begin{tabular}{lllll}
Test name & No enforcer & No side-condition checking & Full enforcer & DataCollider \\\\
\hline
EOF

_make() {
    echo "make $*"
}

cat tests/minimal_direct/bug_table.txt | while read exe_name exe_desc nr_bugs
do
    exe_descr=$(echo $exe_desc | tr '~' ' ')
    _make md_test_dir/${exe_name}.crash_times_dist
    read ctd < <(sed 's/\\/\\\\/g' md_test_dir/${exe_name}.crash_times_dist)
    _make md_test_dir/${exe_name}.dc.crash_times_dist
    read dcctd < <(sed 's/\\/\\\\/g' md_test_dir/${exe_name}.dc.crash_times_dist)
    printf "\hline{}%-20s & %-20s & " "$exe_descr" "$ctd" >&3
    if [ "$nr_bugs" = 1 ]
    then
	_make md_test_dir/${exe_name}~0.S.crash_times_dist
	read esctd < <(sed 's/\\/\\\\/g' md_test_dir/${exe_name}~0.S.crash_times_dist)
	_make md_test_dir/${exe_name}~0.crash_times_dist
	read ectd < <(sed 's/\\/\\\\/g' md_test_dir/${exe_name}~0.crash_times_dist)
	printf "%-20s & %-20s & %-20s \\\\\\\\\n" "$esctd" "$ectd" "$dcctd" >&3
    else
	printf "                     &                       & %-20s\\\\\\\\\n" "$dcctd" >&3
	for i in `seq 0 $(($nr_bugs - 1))`
	do
	    _make md_test_dir/${exe_name}~0.S.crash_times_dist
	    read esctd < <(sed 's/\\/\\\\/g' md_test_dir/${exe_name}~0.S.crash_times_dist)
	    _make md_test_dir/${exe_name}~0.crash_times_dist
	    read ectd < <(sed 's/\\/\\\\/g' md_test_dir/${exe_name}~0.crash_times_dist)
	    printf " & & %-20s & %-20s & \\\\\\\\\n" "$esctd" "$ectd" >&3
	done
    fi
done

echo "\end{tabular}" >&3
