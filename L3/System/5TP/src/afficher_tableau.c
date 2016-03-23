#include <stdio.h>

void	afficher_tableau(int *t, int size)
{
	int	i;

	i = 0;
	printf("[");
	while (i < size - 1)
	{
		printf("%d, ", t[i]);
		++i;
	}
	printf("%d", t[i]);
	printf("]\n");
}
