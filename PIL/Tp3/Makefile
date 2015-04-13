#* ************************************************************************** *#
#*                                                                            *#
#*                                                        :::      ::::::::   *#
#*   Makefile                                           :+:      :+:    :+:   *#
#*                                                    +:+ +:+         +:+     *#
#*   By: tperraut <mythom008@gmail.com>             +#+  +:+       +#+        *#
#*                                                +#+#+#+#+#+   +#+           *#
#*   Created: 2015/02/16 15:07:41 by tperraut          #+#    #+#             *#
#*   Updated: 2015/03/16 16:22:12 by tperraut         ###   ########.fr       *#
#*                                                                            *#
#* ************************************************************************** *#

CC = gcc
LC = lex
YC = yacc
LLIB = -lfl
YLIB = -ly
LOUT = lex.yy.c
YOUT = y.tab.c
CFLAGS = -Wall -Werror -Wextra
SRL = ex01.y
SRC = $(SRL:.y=.c)
NAME = $(SRC:.c=.execute)

all: $(NAME)

%.execute: %.c
	$(CC) -o $@ $< $(YLIB)
%.c: %.y
	$(YC) $<
	mv $(YOUT) $@

clean:
	rm -f $(SRC)

fclean: clean
	rm -f $(NAME)

re: fclean all

.PHONY: clean fclean
