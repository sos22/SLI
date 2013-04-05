#! /bin/sh

# Generate all the job files necessary for a big run of
# minimal_direct.
mkdir jobs
for i in `seq 0 99`
do
    echo "$i $(($i + 1))" > jobs/$i
done
