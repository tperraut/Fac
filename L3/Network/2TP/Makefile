CC = gcc
CFLAGS = -Wall -Werror -Wextra
LIB =
HEADERS = ./include
SRC = \
	  src/serveur_udp.c \
	  src/client_udp.c #\
	  src/serveur_tcp.c \
	  src/client_tcp.c

OBJ = $(SRC:.c=.o)
EXE = $(SRC:.c=.exe)

all: $(EXE)

%.exe:%.o
	$(CC) $(CFLAGS) -o $@ $< -I $(HEADERS)

%.o: %.c
	$(CC) $(CFLAGS) -o $@ -c $< -I $(HEADERS)

clean:
	rm -f $(OBJ)

fclean: clean
	rm -f $(EXE)

re: fclean all
