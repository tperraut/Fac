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

int	main(void)
{
	ssize_t		n;
	socklen_t	from_size;
	char		buf[BUF_SIZE + 1];
	SOCKET		sockfd;
	SOCKADDR_IN	sin = {0}; /*inialization to 0 NEEDED*/
	SOCKADDR_IN	from = {0}; /*inialization to 0 NEEDED*/

	/*socket creation*/
	if((sockfd = socket(AF_INET, SOCK_DGRAM, 0)) == INVALID_SOCKET)
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
	while ((n = recvfrom(sockfd, buf, BUF_SIZE, FLAGS, (SOCKADDR *)&from, &from_size)))
	{
		if(n < 0)
		{
			perror("recvfrom()");
			exit(errno);
		}
		buf[n] = '\0';
		write(1, "server : ", 9);
		write(1, buf, n);
	}
	close(sockfd);
	return (0);
}
