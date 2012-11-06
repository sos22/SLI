#! /bin/sh

exe="$1"
preload="$2"
data="$3"

sample() {
    t=$(mktemp)
    while true
    do
	LD_PRELOAD=$preload $exe > $t && break
    done
    grep "Survived" $t | sed 's/Survived, \([0-9]*\) read events and \([0-9]*\) write events.*/\1 \2/'
}

get_dist() {
    t=$(mktemp)
    check_dist > $t
    if grep -q "Cannot reject normality " "$t"
    then
	mean=$(grep "pop stats" "$t" | sed 's/.*mean = \([-0-9.]*\),.*/\1/')
	sd=$(grep "pop stats" "$t" | sed 's/.*sd = \([-0-9.]*\),.*/\1/')
	echo "\$$mean \\pm $sd\$"
    elif grep -q "Might be uniform" "$t"
    then
	low=$(grep "Might be uniform" "$t" | sed 's/.*uniform(\([0-9.-]*\),.*/\1/')
	high=$(grep "Might be uniform" "$t" | sed 's/.*uniform(\([0-9.-]*\), \([0-9.-]*\)).*/\2/')
	echo "\$\[$low, $high\]\$"
    else
	echo "failed"
    fi
    rm "$t"
}

: > "$data"
for i in `seq 1 10`
do
    sample >> "$data"
done

t_read=$(cut -d' ' -f 1 $data | discard_outliers.py 0.05 | get_dist)
t_write=$(cut -d' ' -f 2 $data | discard_outliers.py 0.05 | get_dist)
if [ "$t_read" != "failed" ] && [ "$t_write" != "failed" ]
then
    echo "Read = $t_read ; Write = $t_write"
    exit 0
fi

echo "Failed with simple characterisation; try with more data" >&2

echo "Stats failed!"
