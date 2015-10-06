.text

main:
    # Chargement de A et B dans $t1 et $t2
    lb $t1, A
    lb $t2, B
    # max($t1, $t2) dans $t3
    bge $t1, $t2, here
	move $t3, $t2
	j end
    # Écriture de $t3 dans C
here:
	move $t3, $t1
end:
	syscall
.data
A : .ascii "2"
B : .ascii "9"

#.data
#A : .ascii "9"
#B : .ascii "2"

C : .ascii "0"
