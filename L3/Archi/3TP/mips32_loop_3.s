.text

main:
    # Chargement de l'adresse de X dans $t6
    lui $t6, 0x1001
    # Chargement de l'adresse de Y dans $t7
    la $t7, 0x10010020
    # Chargement de l'adresse de fin de X dans $t8
    la $t8, 0x10010018
    # Boucle
loop:
    # $t1 = X[i]
	lw $t1, 4($t6)
    # $t2 = X[i-1]
	lw $t2, 0($t6)
    # $t3 = Y[i-1]
    lw $t3, 0($t7)
    # $t3 += $t1 + $t2
    add $t3, $t1, $t2
    # Écriture de $t3 dans Y[i-1]
    sw $t3, 0($t7)
    # Calcul des adresses de X[i] et de Y[i] suivantes
    addi $t6, 4
    addi $t7, 4
    # Condition pour boucler
	bne $t6, $t8, loop
	syscall

.data
# X
.word 0x00000001, 0x00000002, 0x00000003, 0x00000005
.word 0x00000008, 0x0000000D, 0x00000015, 0x00000022
# Y
.word 0x10000000, 0x20000000, 0x30000000, 0x40000000
.word 0x50000000, 0x60000000, 0x7fffffff, 0x8fffffff
