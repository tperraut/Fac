#include "opti.h"

#include <unistd.h>
#include <stdlib.h>

int	main(int ac, char **av)
{
	FILE	*fd;
	t_obj	*a_o;
	int		var;

	if (ac == 2)
	{
		if ((fd = fopen(av[1], "r")) == NULL)
			write(2, "open error\n", 11);
		else
		{
			if ((var = parser(fd, &a_o)) == ER)
				write(2, "parse error\n", 12);
			else
			{
				qsort(&a_o, var, sizeof(t_obj), &(cmp_obj));
				sol_affiche(resolve(a_o, var), var);
			}
		}
	}
	else
		write(1, "usage : ./opti datafile.txt\n", 28);
	return (0);
}
