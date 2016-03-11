#include "opti.h"

#include <stdlib.h>
#include <string.h>

int	parser(FILE *fd, t_obj **pa_o)
{
	char	*line;
	char	*tmp;
	size_t	n;
	ssize_t	get;
	int		var;
	int		i;

	n = 0;
	line = NULL;
	get = 1;
	i = 0;
	var = -1;
	while (i < 4 && get && (get = getline(&line, &n, fd)) != ER)
	{
		if (line[0] != '#')
		{
			++i;
			if (i == 1)
			{
				var = atoi(line);
				if ((*pa_o = (t_obj *)malloc(sizeof(t_obj) * var)) == NULL)
					return (ER);
				++i;
			}
			if (i == 2)
			{
				i = 0;
				tmp = line;
				while (i < var)
				{
					(*pa_o)[i].ci = atoi(tmp);
					tmp = strchr(tmp, (int)' ');
					if (tmp == NULL && i < var - 1)
						return (ER);
					++tmp;
					++i;
				}
				i = 3;
			}
			if (i == 3)
			{
				i = 0;
				tmp = line;
				while (i < var)
				{
					(*pa_o)[i].pi = atoi(tmp);
					tmp = strchr(tmp, (int)' ');
					if (tmp == NULL && i < var - 1)
						return (ER);
					++tmp;
					++i;
				}
				i = 4;
			}
		}
	}
	return ((get == -1) ? ER : var);
}
