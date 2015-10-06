.text

main:
    # Chargement de l'adresse de X dans $t6
    # TODO
    # Chargement de l'adresse de Y dans $t7
    # TODO
    # Chargement de l'adresse de fin de X dans $t8
    # TODO
    # Boucle
    # $t1 = X[i]
    # $t2 = X[i-1]
    # $t3 = Y[i-1]
    # TODO
    # $t3 += $t1 + $t2
    # TODO
    # Écriture de $t3 dans Y[i-1]
    # TODO
    # Calcul des adresses de X[i] et de Y[i] suivantes
    # TODO
    # Condition pour boucler
    # TODO

.data
# X
.word 0x00000001, 0x00000002, 0x00000003, 0x00000005
.word 0x00000008, 0x0000000D, 0x00000015, 0x00000022
# Y
.word 0x10000000, 0x20000000, 0x30000000, 0x40000000
.word 0x50000000, 0x60000000, 0x7fffffff, 0x8fffffff
