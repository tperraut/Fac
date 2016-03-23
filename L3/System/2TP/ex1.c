#include <stdio.h>
#include <time.h>
#define N 100000

int main(void)
{
	int i,j;
	double elapsed;
	clock_t s;
	clock_t e;

	s = clock();
	for (i = 3; i <= N; i++)
	{
		j = 2;
		while ((j * j <= i) && (i % j != 0))
			j++;
		if (i % j != 0)
			printf("%d ", i);
	}
	e = clock();
	elapsed = (double)(e - s) / (double)CLOCKS_PER_SEC;
	printf("\n\ntime=%f\n", elapsed);

	return (0);
}
