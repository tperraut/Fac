#* ************************************************************************** *#
#*                                                                            *#
#*                                                        :::      ::::::::   *#
#*   Makefile                                           :+:      :+:    :+:   *#
#*                                                    +:+ +:+         +:+     *#
#*   By: tperraut <mythom008@gmail.com>             +#+  +:+       +#+        *#
#*                                                +#+#+#+#+#+   +#+           *#
#*   Created: 2015/02/16 15:07:41 by tperraut          #+#    #+#             *#
#*   Updated: 2015/02/16 17:26:14 by tperraut         ###   ########.fr       *#
#*                                                                            *#
#* ************************************************************************** *#

CC = gcc
LC = lex
LLIB = -lfl
LOUT = lex.yy.c
CFLAGS = -Wall -Werror -Wextra
SRL = ex01.lex \
	  ex02.lex \
	  ex03.lex
SRC = $(SRL:.lex=.c)
NAME = $(SRC:.c=.execute)

all: $(NAME)

%.execute: %.c
	$(CC) -o $@ $< $(LLIB)
%.c: %.lex
	$(LC) $<
	mv $(LOUT) $@

clean:
	rm -f $(SRC)

fclean: clean
	rm -f $(NAME)

re: fclean all

.PHONY: clean fclean
