#include "ex05.h"

void	liberer_matrice(int **mat, int n)
{
	int	i;

	i = 0;
	while (i < n)
		liberer_tableau(mat[i++]);
}
