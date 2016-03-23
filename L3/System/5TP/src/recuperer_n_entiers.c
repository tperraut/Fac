#include <stdio.h>
#include "ex05.h"

int	*recuperer_n_entiers(int n)
{
	int	*t;
	int	i;
	int	p;

	i = 0;
	t = allouer_tableau(n, 0);
	printf("Entrez %d nombres :\n", n);
	while (i < n)
	{
		if (i != 0)
			printf("Il manque %d nombres : ", n - i);
		while (i < n && scanf("%d", &p))
			t[i++] = p;
	}
	return (t);
}
