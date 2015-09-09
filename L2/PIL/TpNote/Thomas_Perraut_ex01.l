/*Declarations*/
%{
	int		i = 0;
	int		p = 0;
	int		c = 0;
	int		nb = 0;
	char	*first;
%}
%%

#.*		{}
\n		{}
pour	{p++;}
contre	{c++;}
^[A-Za-z]+/\ ((12:[3-5][0-9]:[0-5][0-9])|(13:[0-3][0-9]:[0-5][0-9]))	{printf ("- %s\n", yytext);}
[0-2][0-9]:[0-5][0-9]:[0-5][0-9]\ [0-2][0-9]:[0-5][0-9]:[0-5][0-9]	{if (strncmp(yytext, (yytext + 9), 8)){nb++;}}
.		{}
%%

#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>

int		main(int ac, char **av)
{
	extern FILE *yyin;
	if (ac <= 2)
	{
		if (ac < 2)
			yyin = stdin;
		else
			yyin = fopen(av[1], "r");
		printf("\nCeux qui ont vote entre 12h30 et 13h30 :\n");
		yylex();
		printf("Nombre de vote : %d\nNombre de pour : %d\nNombre de contre : %d\nNombres de participants ayant modifie leur vote : %d\n", (p + c), p, c, nb);
		fclose (yyin);
	}
	if (ac > 2)
		printf("Too many arguments");
	return (0);
}
