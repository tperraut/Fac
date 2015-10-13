.text

main:
    # Chargement + écriture de A et B
    li $t1, 10
    sw $t1, A
    li $t2, 15
    sw $t2, B
    # Préparation appel fonction
    # TODO
    # fmax
    # TODO
    # Restauration après appel fonction
    # TODO
    # End
    jr $ra

fmax:
    # TODO
    jr $ra

.data
A : .word 0x11111111
B : .word 0x22222222
C : .word 0x33333333
