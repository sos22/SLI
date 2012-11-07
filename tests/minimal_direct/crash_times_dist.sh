#! /bin/sh

exe="$1"
enforcer="$2"
harness_args="$3"
data="$4"

set -e

# First attempt: Can we get away with just claiming it's normal or
# uniform?
SOS22_RUN_FOREVER=1 ./md_test_dir/harness -n 20 $harness_args $enforcer $exe > $data
t=$(mktemp)
check_dist < $data > $t
if grep -q "Cannot reject normality " "$t"
then
    mean=$(grep "pop stats" "$" | sed 's/.*mean = \([-0-9.]*\),.*/\1/')
    sd=$(grep "pop stats" "$t" | sed 's/.*sd = \([-0-9.]*\),.*/\1/')
    rm "$t"
    echo "\$$mean \\pm $sd\$"
    exit 0
fi
if grep -q "Might be uniform" "$t"
then
    low=$(grep "Might be uniform" "$t" | sed 's/.*uniform(\([0-9.-]*\),.*/\1/')
    high=$(grep "Might be uniform" "$t" | sed 's/.*uniform(\([0-9.-]*\), \([0-9.-]*\)).*/\2/')
    rm "$t"
    echo "\$\[$low, $high\]\$"
    exit 0
fi
rm "$t"

echo "Not uniform or gaussian, try resampling" >&2

# Okay, so it failed for both normal and uniform distributions.  See
# if we can characterise by resampling and treating as exponential.
# Need a bit more data for this.
SOS22_RUN_FOREVER=1 ./md_test_dir/harness -n 80 $harness_args $enforcer $exe >> $data
t2=$(mktemp)
./tests/minimal_direct/resample.py < "$data" | head -n 10 > "$t2"
check_dist < "$t2" > "$t"
rm "$t2"
if grep -q "Cannot reject normality " "$t"
then
    mean=$(grep "pop stats" "$t" | sed 's/.*mean = \([-0-9.]*\),.*/\1/')
    sd=$(grep "pop stats" "$t" | sed 's/.*sd = \([-0-9.]*\),.*/\1/')
    rm "$t"
    echo "\$\lambda = $mean \\pm $sd\$"
    exit 0
fi
rm "$t"

echo "Stats failed!"