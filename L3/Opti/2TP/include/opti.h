#ifndef OPTI_H
# define OPTI_H
# include <stdio.h>
# define ER -1

typedef struct	s_obj
{
	int		ref;
	int		ci;
	int		pi;
}				t_obj;

/*Prototype*/
int		parser(FILE *fd, t_obj **pa_o);
void	sol_affiche(int *a_sol, int var);
int		*resolve(t_obj *a_o, int var);
int		cmp_obj(const void *o1, const void *o2);
#endif
