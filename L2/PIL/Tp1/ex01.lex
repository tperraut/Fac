/*Declarations*/

%%
#.*		{
			printf("Commentaire : %s\n", yytext);
		}
\n		{}
.		{}

%%

int		main(void)
{
	yylex();
	return (0);
}
