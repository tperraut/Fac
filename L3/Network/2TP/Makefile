CC = gcc
CFLAGS = -Wall -Werror -Wextra
LIB =
HEADERS = ./include
NAME = tp2.exe
SRC = \
	  src/serveur_tcp.c \
	  src/serveur_udp.c \
	  src/client_tcp.c \
	  src/client_udp.c

OBJ = $(SRC:.c=.o)

all: $(NAME)

$(NAME): $(OBJ)
	$(CC) $(CFLAGS) -o $@ $^ -I $(HEADERS) -I $(LIB)

%.o: %.c
	$(CC) $(CFLAGS) -o $@ -c $< -I $(HEADERS) -I $(LIB)

clean:
	rm -f $(OBJ)

fclean: clean
	rm -f $(NAME)

re: fclean all
