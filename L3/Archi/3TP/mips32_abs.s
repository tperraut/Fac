.text

main:
# Chargement d'un entier positif ou négatif
lui $t1, 0xA000 # Entier négatif
#lui $t1, 0x0A00 # Entier positif
bgez $t1, here # Si t1 positif aller a here
sub $t1, $zero, $t1 # Sinon faire t1 <- 0 - t1
here :
	syscall

.data
