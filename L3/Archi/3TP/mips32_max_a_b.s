.text

main:
# Calcul de l'adresse mémoire de A dans $t7
lui $t7, 0x1001
add $t7, 0x20
# Chargement de A et B dans $t1 et $t2
lb $t1, 0($t7) # A
lb $t2, 1($t7) # B
# max($t1, $t2) dans $t3
bge $t1, $t2, here
move $t3, $t2
j end
# Écriture de $t3 dans C
here:
move $t3, $t2
end:
syscall

.data
.word 0x00001111, 0x22223333, 0x44445555, 0x66667777
.word 0x88889999, 0xAAAABBBB, 0xCCCCDDDD, 0xEEEEFFFF
# A
.ascii "2"
# B
.ascii "9"
# C
.ascii "0"

#.data
#.word 0x00001111, 0x22223333, 0x44445555, 0x66667777
#.word 0x88889999, 0xAAAABBBB, 0xCCCCDDDD, 0xEEEEFFFF
# A
#.ascii "2"
# B
#.ascii "9"
# C
#.ascii "0"
