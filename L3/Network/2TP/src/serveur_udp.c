#include <stdio.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
#include <string.h>

#include "clientserver.h"

int	main(int argc, char **argv)
{
	int			from_size;
	char		buf[BUF_SIZE];
	SOCKET		sockfd;
	SOCKADDR_IN	sin;
	SOCKADDR_IN	from = {0};

	/*socket creation*/
	if((sockfd = socket(AF_INET, SOCK_DGRAM, PF_INET))
			== INVALID_SOCKET)
	{
		perror("socket()");
		exit(errno);
	}
	/*initialize server*/
	sin.sin_family = AF_INET;
	sin.sin_addr.s_addr = htonl(INADDR);
	sin.sin_port = htons(PORT);
	/*interface*/
	if(bind(sockfd, (SOWKADDR *) &addr, sizeof(sin))
			== SOCKET_ERROR)
	{
		perror("bind");
		exit(errno);
	}
	from_size = sizeof(from);
	while ((n = recvfrom(sockfd, buf, BUF_SIZE - 1, FLAGS, (SOCKEADDR *)&from,
					&from_size)))
	{
		if(n < 0)
		{
			perror("recvfrom()");
			exit(errno);
		}
		buf[n] = '\0';
		write(1, buf, n);
	}
	close(sockfd);
	return (0);
}
