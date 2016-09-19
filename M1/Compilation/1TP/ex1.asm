.text

main:	
	li $a0, 4
	li $t0, 6
	jal sum
	li $v0, 1 #code de print_int
	syscall
	
	li $a0, 2
	li $t0, 21
	jal multi
	syscall

	li $a0, 7
	li $t0, 2
	jal divi
	li $t0, 4
	jal sum
	syscall

	li $a0, 10
	li $t0, 5
	jal divi
	li $t0, 6
	jal multi
	neg $a0, $a0
	li $t0, 3
	jal sum
	syscall
	li $v0, 10 #code d'exit
	syscall
divi:
	div $a0, $a0, $t0
	jr $ra
multi:
	mul $a0, $a0, $t0
	jr $ra
sum:
	add $a0, $a0, $t0
	jr $ra
subs:
	sub $a0, $a0, $t0
	jr $ra
.data	