%{
	int	l = 0;
	int	w = 0;
	int	c = 0;
%}
%%
.		{
	c++;
}
[A-Za-z0-9]\ [A-Za-z0-9]	{
	w++;
	c+=3;
}
\n		{
	l++;
}
%%

int		main(void)
{
	yylex();
	printf("Lines : %d\tWords : %d\tChars : %d\n", l, w + 1, c);
	return (0);
}
