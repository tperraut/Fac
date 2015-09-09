%{
	int		l = 0;
	int		s = 0;
	int		t1 = 0;
	int		t2 = 0;
	int		ts = 0;
	float	delta = 1.0;
%}
%%
\|		{
	s++;
	printf("\n");
}
\{[0-9]+\}\{[0-9]+\}		{
	sscanf(yytext, "{%d}{%d}", &t1, &t2);
	usleep(delta * (t1 - ts) * 1000000 / 24);
	l++;
}
[^\|\n]		{
	printf("%s", yytext);
}
\n		{
	printf("\n");
	usleep(delta * (t2 - t1) * 1000000 / 24);
	system("clear");
	ts = t2;
}
%%
#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>

int		main(int ac, char **av)
{
	extern FILE *yyin;
	printf ("Give me the delta mutiplicator : ");
	scanf("%f", &delta);
	if (ac <= 2)
	{
		if (ac < 2)
			yyin = stdin;
		else
			yyin = fopen(av[1], "r");
		yylex();
		printf("\n%s\tLines : %d\tSub : %d\n", av[1], l, (l + s));
		fclose (yyin);
	}
	if (ac > 2)
		printf("Too many arguments");
	return (0);
}
