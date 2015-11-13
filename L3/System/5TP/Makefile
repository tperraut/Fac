CC = gcc
CFLAG = -Wall -Werror -Wextra
HEADER = ./include
NAME = ex05
MAIN = src/main.c
SRC = \
	  src/afficher_matrice.c \
	  src/liberer_matrice.c \
	  src/allouer_matrice.c \
	  src/liberer_tableau.c \
	  src/afficher_tableau.c \
	  src/allouer_tableau.c \
	  src/recuperer_n_entiers.c \

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
