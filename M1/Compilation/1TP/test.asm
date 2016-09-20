#registre required : 6
.text
main:
 li $a0, 4
 sub $a0, $a0, 5
 li $a1, 3
 sub $a0, $a1, $a0
 li $a1, 2
 sub $a0, $a1, $a0
 li $a1, 1
 sub $a0, $a1, $a0
 li $a1, 4
 li $a2, 2
 sub $a2, $a2, 3
 mul $a1, $a2, $a1
 add $a1, $a1, 1
 add $a0, $a1, $a0
#SYSTEM CALL
 li $v0, 1
 syscall
 li $v0, 10
 syscall
