#! /bin/sh

echo "General information:"
echo -n "Date: "
date
echo
echo
echo "Git log:"
git log | head
echo
echo
echo "Git diff:"
git diff | cat
echo
echo
echo "df -h:"
df -h
echo
echo
echo "ls -l:"
ls -l
echo
echo
echo "md5sums:"
md5sum *
echo
echo
echo "contents of this script:"
cat $0
echo
echo
echo "End general information"

