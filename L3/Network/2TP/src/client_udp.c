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
	socklen_t	to_size;
	char		buf[BUF_SIZE];
	HOSTENT		*hostent;
	SOCKET		sockfd;
	SOCKADDR_IN	to;

	if (argc == 2)
	{
		hostent = NULL;
		/*socket creation*/
		if ((sockfd = socket(AF_INET, SOCK_DGRAM, 0)) == INVALID_SOCKET)
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
		to.sin_addr = *(IN_ADDR *) hostent->h_addr;
		to.sin_family = AF_INET;
		to.sin_port = htons(PORT);
		to_size = sizeof(to);
		puts("#Ecrivez vos messages ici#");
		while (fgets(buf, BUF_SIZE, stdin))
		{
			if (sendto(sockfd, buf, strlen(buf), FLAGS, (SOCKADDR *)&to, to_size) < 0)
			{
				perror("sendto()");
				exit(errno);
			}
		}
		close(sockfd);
	}
	else
		puts("usage : ./client_udp.exe HOSTNAME");
	return (0);
}
