#* ************************************************************************** *#
#*                                                                            *#
#*                                                        :::      ::::::::   *#
#*   Makefile                                           :+:      :+:    :+:   *#
#*                                                    +:+ +:+         +:+     *#
#*   By: tperraut <mythom008@gmail.com>             +#+  +:+       +#+        *#
#*                                                +#+#+#+#+#+   +#+           *#
#*   Created: 2015/02/18 12:49:05 by tperraut          #+#    #+#             *#
#*   Updated: 2015/02/18 13:17:38 by tperraut         ###   ########.fr       *#
#*                                                                            *#
#* ************************************************************************** *#

OC=ocamlc
LIB=graphics.cma
SRC=compte.ml \
	decompte.ml \
	mystere.ml \
	jeu.ml
NAME=$(SRC:.ml=.execute)
OBJO=$(SRC:.ml=.cmo)
OBJI=$(SRC:.ml=.cmi)

all: $(NAME)

%.execute: %.ml
	$(OC) -o $@ $<

clean:
	rm -f $(OBJO) $(OBJI)

fclean: clean
	rm -f $(NAME)

re: fclean all

