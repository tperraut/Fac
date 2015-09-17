#include <stdlib.h>
#include <stdio.h>

/*
 *
 */

long long	fibo(int x, int acc, long long r1, long long r2)
{
	long long temp;

	temp = r1 + r2;
	if (x == 0 || x == 1)
		return (1);
	if (acc > x)
		return (r1);
	return (fibo(x, acc + 1, temp, r1));
}


int	main(int ac, char **av)
{
	printf("fibo de %d = %lld\n", atoi(av[1]), fibo(atoi(av[1]), 2, 1, 1));
	return (0);
}
