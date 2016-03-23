#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

void	creer(char *nom_fichier)
{
	int	op;
	op = open(nom_fichier, O_CREAT, S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP);
	if (op == -1)
		write(2, "create fail", 11);
	else
		close(op);
}
