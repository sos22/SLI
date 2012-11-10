#! /bin/bash

exe="$1"
enforcer="$2"
harness_args="$3"
data="$4"

set -e

# First attempt: Can we get away with just claiming it's normal or
# uniform?
SOS22_RUN_FOREVER=1 ./md_test_dir/harness -n 20 -r $harness_args $enforcer $exe > $data
if grep -q "T" "$data"
then
    if grep -v -q "T" "$data"
    then
	echo "\textit{timeout}"
	exit 0
    fi
    n=$(grep "T" "$data" | wc -l)
    echo "\$timeout = ${n}/20"
    exit 0
fi

t=$(mktemp)
< "$data" check_dist > $t
if grep -q "Cannot reject normality " "$t"
then
    mean=$(grep "pop stats" "$t" | sed 's/.*mean = \([-0-9.]*\),.*/\1/')
    sd=$(grep "pop stats" "$t" | sed 's/.*sd = \([-0-9.]*\),.*/\1/')
    rm "$t"
    read mean sd < <(./tests/minimal_direct/sane_round.py "$mean" "$sd")
    echo "\$$mean \\pm $sd\$"
    exit 0
fi
if grep -q "Might be uniform" "$t"
then
    low=$(grep "Might be uniform" "$t" | sed 's/.*uniform(\([0-9.-]*\),.*/\1/')
    high=$(grep "Might be uniform" "$t" | sed 's/.*uniform(\([0-9.-]*\), \([0-9.-]*\)).*/\2/')
    rm "$t"
    read low high < <(./tests/minimal_direct/sane_round_range.py "$low" "$high")
    echo "\$\[$low, $high\]\$"
    exit 0
fi
rm "$t"

echo "Not uniform or gaussian, try resampling" >&2

mk_timeouts() {
    n=$(grep T "$data" | wc -l)
    if [ $n = 0 ]
    then
	return
    fi
    echo -n "; $n timeouts"
}

# Okay, so it failed for both normal and uniform distributions.  See
# if we can characterise by resampling and treating as exponential.
# Need a bit more data for this.
while true
do
    got=$(grep -v "T" $data | wc -l)
    if [ "$got" -ge 100 ]
    then
	break
    fi
    SOS22_RUN_FOREVER=1 ./md_test_dir/harness -n $((100 - $got)) -r $harness_args $enforcer $exe >> $data
done
timeouts=$(mk_timeouts)
t2=$(mktemp)
grep -v T "$data" | ./tests/minimal_direct/resample.py | head -n 10 > "$t2"
check_dist < "$t2" > "$t"
rm "$t2"
if grep -q "Cannot reject normality " "$t"
then
    mean=$(grep "pop stats" "$t" | sed 's/.*mean = \([-0-9.]*\),.*/\1/')
    sd=$(grep "pop stats" "$t" | sed 's/.*sd = \([-0-9.]*\),.*/\1/')
    rm "$t"
    read mean sd < <(./tests/minimal_direct/sane_round.py "$mean" "$sd")
    echo "\$\lambda = $mean \\pm $sd\$${timeouts}"
    exit 0
fi
rm "$t"

grep -v "T" "$data" | ./tests/minimal_direct/characterise_percentiles.py "$timeouts"

