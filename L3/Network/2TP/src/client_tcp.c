#include <stdio.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
#include <string.h>
#include <stdlib.h>
#include <errno.h>

#include "clientserver.h"

int	main(int argc, char **argv)
{
	char		buf[BUF_SIZE];
	HOSTENT		*hostent;
	SOCKET		sockfd;
	SOCKADDR_IN	sin = {0}; /*inialization to 0 NEEDED*/

	if (argc == 2)
	{
		hostent = NULL;
		/*socket creation*/
		if ((sockfd = socket(AF_INET, SOCK_STREAM, 0)) == INVALID_SOCKET)
		{
			perror("socket()");
			exit(errno);
		}
		/*initialize destination*/
		if ((hostent = gethostbyname(argv[1])) == NULL)
		{
			fprintf(stderr, "Unknown host %s.\n", argv[1]);
			exit(EXIT_FAILURE);
		}
		sin.sin_addr = *(IN_ADDR *) hostent->h_addr;
		sin.sin_family = AF_INET;
		sin.sin_port = htons(PORT);
		puts("#Ecrivez vos messages ici#");
		if (connect(sockfd, (SOCKADDR *)&sin, sizeof(SOCKADDR)) == SOCKET_ERROR)
		{
			perror("connect()");
			exit(errno);
		}
		while (fgets(buf, BUF_SIZE, stdin))
		{
			if (send(sockfd, buf, strlen(buf), FLAGS) < 0)
			{
				perror("send()");
				exit(errno);
			}
		}
		close(sockfd);
	}
	else
		puts("usage : ./client_tcp.exe HOSTNAME");
	return (0);
}
