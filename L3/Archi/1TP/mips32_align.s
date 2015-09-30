# Instructions mémoire

.text

main:
	la $t0, X
	la $t1, Y
	la $t2, Z
	la $t3, A
	la $t4, B
	la $t5, C
	la $t6, D
	la $t7, E
	jr $ra

.data
X : .byte 0x10, 0x32, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xEF, 0x01
Y : .half 0x1234, 0x5678
Z : .word 0xABCDEFAC
A : .float 1.5
B : .double 1.5
C : .word 10
D : .asciiz "hello world"
E : .asciiz "fin de l'exercice"
