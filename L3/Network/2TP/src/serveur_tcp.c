#include <stdio.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/wait.h>
#include <netinet/in.h>
#include <netdb.h>
#include <string.h>
#include <stdlib.h>
#include <errno.h>

#include "clientserver.h"

int	indexnotuse(pid_t child[MAX_CLIENT])
{
	int	i;
	int	status;

	i = 0;
	while (i < MAX_CLIENT)
	{
		/*if one slot is empty or one client disconnected*/
		if (child[i] == 0 || waitpid(child[i], &status, WNOHANG))
			return (i);
		++i;
	}
	/*wait if no slot available*/
	wait(&status);
	return (indexnotuse(child));
}

int	main(void)
{
	ssize_t		n;
	int			i;
	char		buf[BUF_SIZE + 1];
	pid_t		father_pid;
	pid_t		child[MAX_CLIENT] = {0};
	socklen_t	from_size;
	SOCKET		sockfd;
	SOCKET		fromfd[MAX_CLIENT];
	SOCKADDR_IN	sin = {0}; /*inialization to 0 NEEDED*/
	SOCKADDR_IN	from = {0}; /*inialization to 0 NEEDED*/

	father_pid = getpid();
	i = 0;
	/*socket creation*/
	if((sockfd = socket(AF_INET, SOCK_STREAM, 0)) == INVALID_SOCKET)
	{
		perror("socket()");
		exit(errno);
	}
	/*initialize server*/
	sin.sin_family = AF_INET;
	sin.sin_addr.s_addr = htonl(INADDR);
	sin.sin_port = htons(PORT);
	/*interface*/
	if(bind(sockfd, (SOCKADDR *) &sin, sizeof(sin)) == SOCKET_ERROR)
	{
		perror("bind()");
		exit(errno);
	}
	from_size = sizeof(from);
	setbuf(stdout, NULL); /*to instant flush with fprintf*/
	do {
		/*server listening*/
		if (listen(sockfd, MAX_CLIENT) == SOCKET_ERROR)
		{
			perror("listen()");
			exit(errno);
		}
		/*connection accepted*/
		if ((fromfd[indexnotuse(child)] = accept(sockfd, (SOCKADDR *)&from, &from_size)) == INVALID_SOCKET)
		{
			perror("accept()");
			exit(errno);
		}
		/*reading*/
		child[i] = fork();
		if (father_pid != getpid())
		{
			fprintf(stdout, "server>>client %d CONNECTED\n", i);
			while ((n = recv(fromfd[i], buf, BUF_SIZE, FLAGS)))
			{
				if(n < 0)
				{
					perror("recv()");
					exit(errno);
				}
				buf[n] = '\0';
				fprintf(stdout, "client %d say : ", i);
				write(1, buf, n);
			}
			fprintf(stdout, "server>>client %d DISCONNECT\n", i);
		}
		else
			++i;
	} while (father_pid == getpid());
	/*close child*/
	close(fromfd[i]);
	return (0);
}
