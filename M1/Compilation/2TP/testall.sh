#!/bin/bash


op=$1
shift
if [ -z $* ]
then
	echo "Usage : ./testall.sh [0 or 1] file1 file2 ..."
	exit 0
fi
for p in $@
do
	echo -n "FILE_NAME : "
	echo $p
	echo ""
	echo -n "INPUT : "
	cat $p
	echo ""
	echo -n "INTERPRETER : "
	./compilo -i $p
	echo ""
	echo -n "COMPILER : "
	./compilo $p > test.asm
	echo `java -jar ../Mars4_5.jar test.asm` |awk '{print $NF}'
	if [ $op = "1" ]
	then
		echo ""
		echo "MIPS_CODE :"
		cat test.asm
	fi
	echo "###############################"
done
