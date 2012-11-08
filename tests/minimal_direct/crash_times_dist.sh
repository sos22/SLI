#! /bin/bash

exe="$1"
enforcer="$2"
harness_args="$3"
data="$4"

set -e

# First attempt: Can we get away with just claiming it's normal or
# uniform?
SOS22_RUN_FOREVER=1 ./md_test_dir/harness -n 20 $harness_args $enforcer $exe > $data
t=$(mktemp)
mk_timeouts() {
    n=$(grep T "$data" | wc -l)
    if [ $n = 0 ]
    then
	return
    fi
    echo -n "; $n timeouts"
}
timeouts=$(mk_timeouts)
grep -v "T" $data | check_dist > $t
if grep -q "Cannot reject normality " "$t"
then
    mean=$(grep "pop stats" "$t" | sed 's/.*mean = \([-0-9.]*\),.*/\1/')
    sd=$(grep "pop stats" "$t" | sed 's/.*sd = \([-0-9.]*\),.*/\1/')
    rm "$t"
    echo "\$$mean \\pm $sd\$${timeouts}"
    exit 0
fi
if grep -q "Might be uniform" "$t"
then
    low=$(grep "Might be uniform" "$t" | sed 's/.*uniform(\([0-9.-]*\),.*/\1/')
    high=$(grep "Might be uniform" "$t" | sed 's/.*uniform(\([0-9.-]*\), \([0-9.-]*\)).*/\2/')
    rm "$t"
    echo "\$\[$low, $high\]\$${timeouts}"
    exit 0
fi
rm "$t"

if ! [ -z "$timeouts" ]
then
    echo "Failed${timeouts}"
    exit 0
fi

echo "Not uniform or gaussian, try resampling" >&2

# Okay, so it failed for both normal and uniform distributions.  See
# if we can characterise by resampling and treating as exponential.
# Need a bit more data for this.
SOS22_RUN_FOREVER=1 ./md_test_dir/harness -n 80 $harness_args $enforcer $exe >> $data
t2=$(mktemp)
grep -v T "$data" | ./tests/minimal_direct/resample.py | head -n 10 > "$t2"
check_dist < "$t2" > "$t"
timeouts=$(mk_timeouts)
rm "$t2"
if grep -q "Cannot reject normality " "$t"
then
    mean=$(grep "pop stats" "$t" | sed 's/.*mean = \([-0-9.]*\),.*/\1/')
    sd=$(grep "pop stats" "$t" | sed 's/.*sd = \([-0-9.]*\),.*/\1/')
    rm "$t"
    echo "\$\lambda = $mean \\pm $sd\$${timeouts}"
    exit 0
fi
rm "$t"

echo "Stats failed!"
