%{
#include <stdio.h>
#include <ctype.h>
%}

%token CHIFFRE

%%
ligne	: expr {printf("%d\n", $1);}
		;
expr	: expr '+' terme {$$ = $1 + $3;}
		| terme
		;
terme	: terme '*' facteur {$$ = $1 * $3;}
		| facteur
		;
facteur : '(' expr ')' {$$ = $2;}
		| CHIFFRE
		;

%%

yylex()
{
	int	c;
	c = getchar();
	if (isdigit(c))
	{
		yylval = c - '0';
		return (CHIFFRE);
	}
	else if (c == '\n')
		return (0);
	else
		return (c);
}