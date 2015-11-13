#include "ex05.h"
#include <stdlib.h>

int	**allouer_matrice(int li, int co, int val)
{
	int	**mat;
	int	i;

	i = 0;
	mat = (int **)malloc(sizeof(int *) * li);
	while (i < li)
		mat[i++] = allouer_tableau(co, val);
	return (mat);
}
