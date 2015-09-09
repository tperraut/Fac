/*Declarations*/

%%
0/(11)*		{
				printf("a");
			}
01/(11)*	{
				printf("b");
			}
11/(11)*	{
				printf("c");
			}

.		{}
%%

int		main(void)
{
	yylex();
	return (0);
}
