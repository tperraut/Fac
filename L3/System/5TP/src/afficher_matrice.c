#include <stdio.h>

void	afficher_matrice(int **mat, int li, int co)
{
	int	i;
	int	j;

	i = 0;
	while (i < li)
	{
		j = 0;
		printf("(");
		while (j < co - 1)
			printf("%d,", mat[i][j++]);
		printf("%d)\n", mat[i][j]);
		++i;
	}
}
