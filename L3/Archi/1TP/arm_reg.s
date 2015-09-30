@ Alignement mémoire
LDR r0, =A @ Chargement adresse de A
MOV r1, #4
LDR r2, [r0, #4]
LDR r3, [r0, #4] !
LDR r4, [r0], #8
LDR r5, [r0, -r1, LSL#1]
SWI 0x11 @ Stop program execution

.data
A: .byte 0x10, 0X32, 0x54, 0x76, 0x98, 0xBA, 0xDC, 0xEF, 0x01
