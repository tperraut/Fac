#include <stdio.h>

void	sol_affiche(int *a_sol, int var)
{
	int	i;

	i = 0;
	while (i < var)
	{
		printf("x%d = %d\n", i + 1, a_sol[i]);
		++i;
	}
}
