#! /bin/bash

exe="$1"
preload="$2"
data="$3"

sample() {
    t=$(mktemp)
    cntr=0
    while [ $cntr -lt 100 ]
    do
	LD_PRELOAD=$preload $exe > $t && break
	cntr=$(($cntr + 1))
    done
    grep "Survived" $t | sed 's/Survived, \([0-9]*\) read events and \([0-9]*\) write events.*/\1 \2/'
    rm -f "$t"
}

get_dist() {
    t2=$(mktemp)
    cat > "$t2"
    t=$(mktemp)
    cat "$t2" | check_dist > $t
    if grep -q "Cannot reject normality " "$t"
    then
	mean=$(grep "pop stats" "$t" | sed 's/.*mean = \([-0-9.]*\),.*/\1/')
	sd=$(grep "pop stats" "$t" | sed 's/.*sd = \([-0-9.]*\),.*/\1/')
	read mean sd < <(./tests/minimal_direct/sane_round.py "$mean" "$sd")
	echo "\$$mean \\pm $sd\$"
    else
	cat "$t2" | ./tests/minimal_direct/characterise_percentiles.py ""
    fi
    rm "$t"
    rm "$t2"
}

: > "$data"
for i in `seq 1 10`
do
    sample >> "$data"
done

t_read=$(cut -d' ' -f 1 $data | discard_outliers.py 0.05 | get_dist)
t_write=$(cut -d' ' -f 2 $data | discard_outliers.py 0.05 | get_dist)
echo "Read = $t_read ; Write = $t_write"
exit 0
