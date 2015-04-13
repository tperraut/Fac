%{
#include <stdio.h>
#include <ctype.h>
#include <stdlib.h>
%}

%token CHIFFRE

%%
ligne	: expr {printf("%d\n", $1);}
		;
expr	: expr '+' terme {$$ = $1 + $3;}
		| expr '-' terme {$$ = $1 - $3;}
		| terme
		;
terme	: terme '*' facteur {$$ = $1 * $3;}
		| terme '/' facteur
			{
				if ($3 == 0)
				{
					printf("Division by 0 is forbiden\n");
					return ;
				}
				$$ = $1 / $3;
			}
		| facteur
		;
facteur : '(' expr ')' {$$ = $2;}
		| CHIFFRE
		;
%%