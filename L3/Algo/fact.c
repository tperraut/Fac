#include <stdio.h>

unsigned long long	fact(int x, unsigned long long c)
{
	if (x == 0)
		return (c);
	return (fact(x - 1, c * x));
}

int	main(void)
{
	printf("factorielle de 20 = %llu\n", fact(20, 1));
	return (0);
}
