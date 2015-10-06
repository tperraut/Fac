.text

main:
    # Chargement adresse dans $t7 de l'adresse de X
    lui $t6, 0x1001
    # Chargement de l'adresse de fin de X dans $t8
    li $t8, 0x10010040
    # s = 0 ($t2 = 0)
    move $t3, $zero
    # Boucle
loop:
    # $t1 = X[i]
    lw $t1, 0($t6)
    # $t2 += $t1
    blez $t1, jump
    add $t3, $t3, $t1
    # Calcul de l'adresse de X[i] suivante
jump:
    addi $t6, 4
    # Condition pour boucler
    bne $t6, $t8, loop
    # Écriture de $t3 dans s
    sw $t3, 0($t6)

.data
# X
.word 0x00000001, 0xA0000010, 0x00000100, 0xA0001000
.word 0x00010000, 0xA0100000, 0x01000000, 0xA0000000
.word 0xA0000002, 0x00000020, 0xA0000200, 0x00002000
.word 0xA0020000, 0x00200000, 0xA2000000, 0x20000000
# s
.word 0xffffffff
