#include <sys/stat.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>

void	ajout(char *nom_fichier)
{
	char	*line;
	int		i;
	int		stream;
	size_t	n;
	int		get;

	i = 0;
	line = NULL;
	if ((stream = open(nom_fichier, O_RDWR | O_APPEND | O_CREAT,  S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP))
			&& stream == -1)
	{
		write(2, "open fail", 9);
		return;
	}
	while (i < 4)
	{
		n = 0;
		if ((get = getline(&line, &n, stdin)) && get == -1)
		{
			write(2, "get error", 9);
			return;
		}
		write(stream, line, n);
		++i;
	}
	close(stream);
	free(line);
}
