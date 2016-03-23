#include "opti.h"

int		cmp_obj(const void *o1, const void *o2)
{
	t_obj	*oo1;
	t_obj	*oo2;
	float	c1;
	float	c2;

	oo1 = (t_obj *)o1;
	oo2 = (t_obj *)o2;
	c1 = (float)oo1->ci / oo1->pi;
	c2 = (float)oo2->ci / oo2->pi;
	if (c1 > c2)
		return (1);
	if (c1 < c2)
		return (-1);
	return (0);
}
