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

all: $(EXE) $(OBJ)
	@echo -e "\e[1;32mBuild Done\e[0m"

%.exe:%.o
	$(CC) $(CFLAGS) -o $@ $< -I $(HEADERS)
	cp $@ ./

%.o: %.c
	$(CC) $(CFLAGS) -o $@ -c $< -I $(HEADERS)

clean:
	rm -f $(OBJ)

fclean: clean
	rm -f $(EXE)
	rm -f *.exe

re: fclean all
