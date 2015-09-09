%{
	#include "y.tab.h"
	extern int yylval;
%}
%%

[0-9]+	{
			yylval = atoi(yytext);
			return (CHIFFRE);
		}
[a-z]	{
			yylval = (int)(yytext[0] - 'a');
			return (LETTRE);
		}
\ |\t	{}
->		{
			return '>';
		}
\\\/		{
			return 'V';
		}
\/\\		{
			return '^';
		}
.	{
			return (yytext[0]);
		}
%%
