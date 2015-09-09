%{
#include <stdio.h>
#include <ctype.h>
#include <stdlib.h>
int	tab[26];
%}

%token CHIFFRE
%token LETTRE

%%
input	: ligne '\n' ligne '\n' ligne '\n' ligne
		;
ligne	: impl	{printf("%d\n", $1);}
		| declare
		;
declare : LETTRE '=' CHIFFRE	{tab[$1] = $3;printf("%c")}
		;
impl	: impl '>' or	{$$ = !$1 || $3;}
		| or
		;
or		: or 'V' and	{$$ = $1 || $3;}
		| and
		;
and		: and '^' expr		{$$ = $1 && $3;}
		| expr
		;
expr	: expr '+' terme	{$$ = $1 + $3;}
		| expr '-' terme	{$$ = $1 - $3;}
		| terme
		;
terme	: terme '*' not	{$$ = $1 * $3;}
		| terme '/' not
			{
				if ($3 == 0)
				{
					printf("Division by 0 is forbiden\n");
					return ;
				}
				$$ = $1 / $3;
			}
		| not
		;
not		: '~' not		{$$ = !$2;}
		| '~' facteur	{$$ = !$2;}
		| facteur
		;
facteur : '(' impl ')'	{$$ = $2;}
		| CHIFFRE
		| LETTRE	{$$ = tab[$1];}
		;
%%
