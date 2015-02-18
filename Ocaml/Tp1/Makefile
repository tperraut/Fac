#* ************************************************************************** *#
#*                                                                            *#
#*                                                        :::      ::::::::   *#
#*   Makefile                                           :+:      :+:    :+:   *#
#*                                                    +:+ +:+         +:+     *#
#*   By: tperraut <mythom008@gmail.com>             +#+  +:+       +#+        *#
#*                                                +#+#+#+#+#+   +#+           *#
#*   Created: 2015/02/18 12:49:05 by tperraut          #+#    #+#             *#
#*   Updated: 2015/02/18 13:13:13 by tperraut         ###   ########.fr       *#
#*                                                                            *#
#* ************************************************************************** *#

OC=ocamlc
LIB=graphics.cma
SRC=approx_pi.ml \
	bonjour.ml \
	cardioide.ml \
	dice_roller.ml \
	hello.ml \
	ieme.ml \
	leap_year.ml \
	mandelbrot.ml \
	somme.ml
NAME=$(SRC:.ml=.execute)
OBJO=$(SRC:.ml=.cmo)
OBJI=$(SRC:.ml=.cmi)

all: $(NAME)

%.execute: %.ml
	$(OC) -o $@ $(LIB) $<

clean:
	rm -f $(OBJO) $(OBJI)

fclean: clean
	rm -f $(NAME)

re: fclean all

