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
SRY = ex01.y
SRL = $(SRY:.y=.lex)
SRCY = $(SRY:.y=.c)
NAME = $(SRY:.y=.execute)

all:
	$(LC) $(SRL)
	$(YC) -d $(SRY)
	$(CC) -o $(NAME) $(YOUT) $(LOUT) $(YLIB) $(LLIB)

clean:
	rm -f $(LOUT) $(YOUT) $(YOUT:.c=.h)

fclean: clean
	rm -f $(NAME)

re: fclean all

.PHONY: clean fclean
