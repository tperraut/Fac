# Instructions mémoire

.text

main:
	la $t0, X
	lw $t1, 0($t0)
	lw $t2, 8($t0)
	lb $t3, 5($t0)
	lh $t4, 2($t0)
	lhu $t5, 6($t0)
	lbu $t6, 3($t0)
	la $t0, Y
	lw $t7, 0($t0)
	lw $s0, 4($t0)
	jr $ra

.data
X: .byte 0x10, 0x32, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xEF, 0x01
Y: .word 0x76543210, 0xEFDCBA98




