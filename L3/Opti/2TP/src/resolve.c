#include "opti.h"

#include <stdlib.h>

int		*resolve(t_obj *a_o, int var)
{
	int	*a_var;

	if (a_o)
		var++;
	if ((a_var = (int *)malloc(sizeof(int) * var)) == NULL)
		return (NULL);
	return (a_var);
}
