.text

main:
    # Chargement + écriture
    la $t8, V
    li $t1, 0x1A
    sb $t1, 0($t8)
    li $t1, 0x19
    sb $t1, 1($t8)
    li $t1, 0x18
    sb $t1, 2($t8)
    li $t1, 0x17
    sb $t1, 3($t8)
    li $t1, 0x16
    sb $t1, 4($t8)
    li $t1, 0x15
    sb $t1, 5($t8)
    li $t1, 0x14
    sb $t1, 6($t8)
    li $t1, 0x13
    sb $t1, 7($t8)
    li $t1, 0x12
    sb $t1, 8($t8)
    li $t1, 0x11
    sb $t1, 9($t8)
    # Préparation tri
    move $t7, $ra
    # tri
    jal tri
    # Restauration après tri
    move $ra, $t7
    # End
    jr $ra

tri:
	move $t9, $ra
    # Addresse de fin pour v[i]
    la $t4, 10($t8)
    # Addresse de v[i + 1]
    la $t6, 1($t8)
    loopi:
        # Addresse de v[i] # i
        addi $t4, $t4, -1
        # v[i]
        lb $t1, 0($t4)
        # Addresse de fin pour v[j] # j
        move $t5, $t4
        # Addresse de v[j + 1]
        loopj:
			addi $t5, $t5, -1
            # Addresse de v[j]
            # v[j]
            lb $t2, 0($t5)
            # if (v[j] < v[i])
			bgt $t1, $t2, next
            	jal change
			next:
        # loopj
        bne $t5, $t8, loopj
    # loopi
    bne $t4, $t6, loopi
	move $ra, $t9
    jr $ra

change:
    move $t0, $t2
	move $t2, $t1
	move $t1, $t0

	sb $t2, 0($t5)
	sb $t1, 0($t4)
    jr $ra

.data
V : .byte 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff
