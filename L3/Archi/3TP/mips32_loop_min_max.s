.text

main:
    # Chargement de l'adresse de X dans $t7
    la $t7, 0x10010000
    # Chargement de l'adresse de fin de X dans $t8
    la $t8, 0x10010020
    # Initialisation de min et max ($t1 et $t2)
    lw $t1, 0($t7)
    lw $t2, 0($t7)
    # Boucle
loop:
    # $t3 = X[i]
    lw $t3, 0($t7)
    # min
    ble $t1, $t3, nmin
	move $t1, $t3
nmin:
    # max
	bge $t2, $t3, nmax
	move $t2, $t3
nmax:
    # Calcul de l'adresses de X[i] suivante
    addi $t7, 4
    # Condition pour boucler
    bne $t7, $t8, loop
    # Écriture de min et max
    sw $t1, 0($t7)
    sw $t2, 4($t7)
	syscall

.data
# X
.word 0x00000004, 0x00000003, 0x00000002, 0x00000001
.word 0x00000005, 0x00000006, 0x00000007, 0x00000008
# min
MIN : .word 0x11111111
# max
MAX : .word 0x22222222
