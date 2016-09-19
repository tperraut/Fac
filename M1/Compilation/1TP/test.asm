.text
main:
 li $a0, 2
 sub $a0, $a0, 3
 li $a1, 4
 mul $a0, $a0, $a1
 add $a0, $a0, 1
#SYSTEM CALL
 li $v0, 1
 syscall
 li $v0, 10
 syscall
