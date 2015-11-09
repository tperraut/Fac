#include <stdlib.h>

int *allouer_tableau(int dim, int val)
{
	int	*t;
	int	i;

	i = 0;
	t = (int *)malloc(sizeof(int) * dim);
	while (i < dim)
	{
		t[i] = val;
		++i;
	}
	return (t);
}
