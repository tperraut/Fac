#ifndef CLIENTSERVER_H
# define CLIENTSERVER_H
# define PORT 9600
# define INVALID_SOCKET -1
# define SOCKET_ERROR -1
# define BUF_SIZE 2048
# define INADDR 0x7F000001
# define FLAGS 0

typedef int		SOCKET;
typedef struct	sockaddr_in SOCKADDR_IN;
typedef struct	sockaddr SOCKADDR;
typedef struct	in_addr IN_ADDR;
typedef struct	hostent HOSTENT;
#endif
