#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>

void	afficher(char *nom_fichier)
{
	FILE	*op;
	char	*line;
	size_t	n;
	int		get;

	line = NULL;
	n = 0;
	op = fopen(nom_fichier, "r");
	if ((get = getline(&line, &n, op)) == -1 || op == NULL )
	{
		write(2, "afficher fail\n", 9);
		return;
	}
	while (get > 0)
	{
		write(1, line, get);
		get = getline(&line, &n, op);
	}
	free(line);
	fclose(op);
}
