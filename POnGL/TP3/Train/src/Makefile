# **************************************************************************** #
#                                                                              #
#                                                         :::      ::::::::    #
#    Makefile                                           :+:      :+:    :+:    #
#                                                     +:+ +:+         +:+      #
#    By: tperraut <marvin@42.fr>                    +#+  +:+       +#+         #
#                                                 +#+#+#+#+#+   +#+            #
#    Created: 2014/11/06 15:54:33 by tperraut          #+#    #+#              #
#*   Updated: 2015/02/18 00:57:10 by tperraut         ###   ########.fr       *#
#                                                                              #
# **************************************************************************** #

CC = javac
AR = jar -cf
NAME = Main
SRC = Main.java

OBJ = ./obj

all: $(NAME)

$(NAME): $(OBJ)

$(OBJ): $(SRC)
	mkdir $@
	$(CC) $< -d $(OBJ)

clean:
	rm -rf $(OBJ)

fclean: clean

re: fclean all

test: all
	java $(NAME)
