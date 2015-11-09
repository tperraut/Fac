#include "ex05.h"
#include <stdio.h>

int	main(void)
{
	int	*t;
	int	*t1;
	int	*t2;
	int	**mat;
	int	**mat1;

	//Q2
	t = allouer_tableau(SIZE, 1);
	//Q3
	t1 = recuperer_n_entiers(SIZE / 2);
	//Q4 et test Q2
	afficher_tableau(t, SIZE);
	liberer_tableau(t);
	t2 = allouer_tableau(SIZE, 5);
	afficher_tableau(t, SIZE);
	afficher_tableau(t2, SIZE);
	//test Q3
	afficher_tableau(t1, SIZE / 2);
	//Q5
	//t = recuperer_entiers(7, 15);
	//afficher_tableau(t, 21);
	//Q6
	mat = allouer_matrice(SIZE / 2, SIZE / 2, 2);
	printf("Matrice %dx%d\n", SIZE / 2, SIZE / 2);
	//test Q7
	afficher_matrice(mat, SIZE / 2, SIZE / 2);
	printf("\n");
	//Q7
	liberer_matrice(mat, SIZE / 2);
	mat1 = allouer_matrice(SIZE / 2, SIZE / 2, 3);
	//test liberer_matrice
	afficher_matrice(mat, SIZE / 2, SIZE / 2);
	printf("\n");
	afficher_matrice(mat1, SIZE / 2, SIZE / 2);
	return (0);
}
