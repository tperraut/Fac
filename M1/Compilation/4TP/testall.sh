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
	echo -ne "\e[97;100mFILE_NAME\e[0m : "
	echo -e "\033[1m$p\033[0m"
	echo -ne "\e[97;100mINPUT\e[0m : "
	cat $p
	echo -ne "\e[97;100mINTERPRETER\e[0m : "
	i=`./compilo -i $p`
	echo -e "\033[1m$i\033[0m"
	echo -ne "\e[97;100mCOMPILER\e[0m : "
	./compilo $p > test.asm
	c=$(java -jar ../Mars4_5.jar nc test.asm)
	echo -e "\033[1m$c\033[0m"
	if [ "$i" != "$c" ]
	then
		echo -e "\e[1;97;101m[FAIL]\e[0m"
	else
		echo -e "\e[1;90;102m[OK]\e[0m"
	fi
	if [ $op = "1" ] || [ "$i" != "$c" ] && [ $op = "3" ]
	then
		echo ""
		echo -e "\e[97;100mMIPS_CODE\e[0m"
		cat test.asm
	fi
	echo "###############################"
done
