CC = gcc
CFLAG = -Wall -Werror -Wextra
HEADER = ./include
NAME = tp7
MAIN = src/main.c
SRC = \
	  src/ajout.c \
	  src/creer.c \
	  src/afficher.c \

OBJ = $(SRC:.c=.o)

all: $(NAME)

$(NAME): $(OBJ)
	$(CC) $(CFLAG) -o $@ $(MAIN) $^ -I $(HEADER)

%.o: %.c
	$(CC) $(CFLAG) -o $@ -c $< -I $(HEADER)

clean:
	rm -f $(OBJ)

fclean: clean
	rm -f $(NAME)

re: fclean all

test: all
	./ex05
