#! /bin/bash

name="$1"

mkdir "$name" || exit 1

cp florida/* "$name"
ln -s ${PWD}/2011-12-21b/crash_summaries ${name}

in_script=$(mktemp)
cat > ${in_script} <<EOF
cd ${name} || exit
date
git log | head
git diff | cat
(cd /local/scratch/sos22/mysql-5.5.6-rc ; git log | head ; git diff | cat)
ls -l
md5sum *
make -C.. || exit
./florida.sh
EOF

chmod +x ${in_script}

script -c ${in_script} -f ${name}/florida.log

rm ${in_script}
