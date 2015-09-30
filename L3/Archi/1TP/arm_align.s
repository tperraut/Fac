@ Alignement mémoire
LDR r0, =A @ Chargement adresse de A
LDR r1, =B
LDR r2, =C
LDR r3, =D
SWI 0x11 @ Stop program execution

.data
A: .byte 0x39, 0x32, 0x24, 0xAB, 0xDA
B: .word 0x98765432, 0xFA00, 0xFEDCBA98
C: .asciz "Hello world"
D: .word 345
