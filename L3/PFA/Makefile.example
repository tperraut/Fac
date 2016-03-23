# **************************************************************************** #
#                                                                              #
#                                                         :::      ::::::::    #
#    Makefile                                           :+:      :+:    :+:    #
#                                                     +:+ +:+         +:+      #
#    By: tperraut <tperraut@student.42.fr>          +#+  +:+       +#+         #
#                                                 +#+#+#+#+#+   +#+            #
#    Created: 2015/03/30 16:05:48 by tperraut          #+#    #+#              #
#    Updated: 2015/03/31 19:13:19 by tperraut         ###   ########.fr        #
#                                                                              #
# **************************************************************************** #

OC=ocamlc
LIB=graphics.cma
SRC= \
	 TP2.ml
NAME=$(SRC:.ml=.exe)
OBJO=$(SRC:.ml=.cmo)
OBJI=$(SRC:.ml=.cmi)

all: $(NAME)

%.exe: %.ml
	$(OC) -o $@ $(LIB) $<

clean:
	rm -f $(OBJO) $(OBJI)

fclean: clean
	rm -f $(NAME)

re: fclean all

