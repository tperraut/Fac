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
	i=`./compilo -i $p`
	echo $i
	echo ""
	echo -n "COMPILER : "
	./compilo $p > test.asm
	c=$(echo $(java -jar ../Mars4_5.jar test.asm) | awk '{print $NF}')
	echo $c
	if [ "$i" != "$c" ]
	then
		echo -e "\033[31;1mFAIL\033[0m"
	else
		echo -e "\033[32;1mOK\033[0m"
	fi
	if [ $op = "1" ] || [ "$i" != "$c" ]
	then
		echo ""
		echo "MIPS_CODE :"
		cat test.asm
	fi
	echo "###############################"
done
