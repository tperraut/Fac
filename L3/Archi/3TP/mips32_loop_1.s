.text

main:
    # Chargement de l'adresse de X dans $t6
	lui $t6, 0x1001
    # Chargement de l'adresse de Y dans $t7
    lui $t7, 0x1001
	addi $t7, 0x0020
    # Chargement de l'adresse de fin de X dans $t8
    lui $t8, 0x1001
	addi $t8, 0x0020
	# s = 0 ($t3 = 0)
    li $t3, 0x00000000
    # Boucle
loop:
    # $t1 = X[i]
    lw $t1, 0($t6)
    # $t2 = Y[i]
    lw $t2, 0($t7)
    # $t3 += $t1 + $t2
    add $t3, $t3, $t1
    add $t3, $t3, $t2
    # Calcul des adresses de X[i] et de Y[i] suivantes
    addi $t6, 4
    addi $t7, 4
    # Condition pour boucler
    bne $t6, $t8, loop
    # Écriture de $t3 dans s
    sw $t3, 32($t8)
	syscall
.data
# X
.word 0x00000001, 0x00000010, 0x00000100, 0x00001000
.word 0x00010000, 0x00100000, 0x01000000, 0x10000000
# Y
.word 0x00000002, 0x00000020, 0x00000200, 0x00002000
.word 0x00020000, 0x00200000, 0x02000000, 0x20000000
# s
.word 0xffffffff
