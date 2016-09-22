#base registre required : 24
.text
main:
 li $a0, 2
 mul $a0, $a0, 4
 mul $a0, $a0, 4
 li $a1, 2
 mul $a1, $a1, 4
 add $a0, $a1, $a0
 mul $a0, $a0, 4
 li $a1, 2
 mul $a1, $a1, 4
 add $a0, $a1, $a0
 li $a1, 2
 mul $a1, $a1, 4
 mul $a1, $a1, 4
 li $a2, 2
 mul $a2, $a2, 4
 add $a1, $a2, $a1
 mul $a1, $a1, 4
 li $a2, 2
 mul $a2, $a2, 4
 add $a1, $a2, $a1
 mul $a0, $a1, $a0
 li $a1, 2
 mul $a1, $a1, 4
 mul $a1, $a1, 4
 li $a2, 2
 mul $a2, $a2, 4
 add $a1, $a2, $a1
 mul $a1, $a1, 4
 li $a2, 2
 mul $a2, $a2, 4
 add $a1, $a2, $a1
 li $a2, 2
 mul $a2, $a2, 4
 mul $a2, $a2, 4
 li $a3, 2
 mul $a3, $a3, 4
 add $a2, $a3, $a2
 mul $a2, $a2, 4
 li $a3, 2
 mul $a3, $a3, 4
 add $a2, $a3, $a2
 mul $a1, $a2, $a1
 add $a0, $a1, $a0
 li $a1, 2
 mul $a1, $a1, 4
 mul $a1, $a1, 4
 li $a2, 2
 mul $a2, $a2, 4
 add $a1, $a2, $a1
 mul $a1, $a1, 4
 li $a2, 2
 mul $a2, $a2, 4
 add $a1, $a2, $a1
 li $a2, 2
 mul $a2, $a2, 4
 mul $a2, $a2, 4
 li $a3, 2
 mul $a3, $a3, 4
 add $a2, $a3, $a2
 mul $a2, $a2, 4
 li $a3, 2
 mul $a3, $a3, 4
 add $a2, $a3, $a2
 mul $a1, $a2, $a1
 li $a2, 2
 mul $a2, $a2, 4
 mul $a2, $a2, 4
 li $a3, 2
 mul $a3, $a3, 4
 add $a2, $a3, $a2
 mul $a2, $a2, 4
 li $a3, 2
 mul $a3, $a3, 4
 add $a2, $a3, $a2
 li $a3, 2
 mul $a3, $a3, 4
 mul $a3, $a3, 4
 li $a4, 2
 mul $a4, $a4, 4
 add $a3, $a4, $a3
 mul $a3, $a3, 4
 li $a4, 2
 mul $a4, $a4, 4
 add $a3, $a4, $a3
 mul $a2, $a3, $a2
 add $a1, $a2, $a1
 add $a0, $a1, $a0
#SYSTEM CALL
 li $v0, 1
 syscall
 li $v0, 10
 syscall
