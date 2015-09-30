# 6 premières valeurs de la suite de Fibonnacci sans boucle

.text

main:
	la $t0, X
	add $t1, $zero, $zero
	sw $t1, 0($t0)
	addi $t2, $zero, 1
	sw $t2, 4($t0)
	# Code à compléter (sans boucle) pour les 4 valeurs suivantes
	jr $ra

.data
X: .word 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
