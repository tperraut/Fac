#!/bin/bash

if [ $# -ne 1 ]
then
echo "Usage : ./compress folder_name"
exit 0
fi
name=Perraut_Frelikh
namegz="$name.tar.gz"
cp -r $1 $name
echo -e "\033[32mcleanup objects files\033[0m"
make clean -C $name > /dev/null
echo -e "\033[32;1m...Compression...\033[0m"
tar -zcvf $namegz $name
echo -e "\033[32;1m...Finished...\033[0m"
rm -r $name
