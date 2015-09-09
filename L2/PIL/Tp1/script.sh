#!bin/bash

# Initialisation
i = 0
# Boucle de 0 a 100
while [ $i -lt 100]
do
	i = $(($i + 1)) # Increment
	echo $i			# Affichage

