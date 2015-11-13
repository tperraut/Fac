#include <unistd.h>
#include <signal.h>

void	child(void)
{
	sleep(4);
	write(1, "fini\n", 5);
}

void	father(pid_t pid)
{
	sleep(2);
	write(1, "bye\n", 4);
	kill(pid, 1);
	execl("./ex1", "", (char *)NULL);
}
int	main(void)
{
	pid_t pid;

	pid = fork();
	switch (pid) {
		case -1:
			return (-1);
			break;
		case 0:
			child();
			break;
		default:
			father(pid);
			break;
	}

	return (1);
}
