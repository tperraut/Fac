# **************************************************************************** #
#                                                                              #
#                                                         :::      ::::::::    #
#    Makefile                                           :+:      :+:    :+:    #
#                                                     +:+ +:+         +:+      #
#    By: tperraut <mythom008@gmail.com>             +#+  +:+       +#+         #
#                                                 +#+#+#+#+#+   +#+            #
#    Created: 2014/11/06 15:54:33 by tperraut          #+#    #+#              #
#*   Updated: 2015/03/18 14:36:10 by tperraut         ###   ########.fr       *#
#                                                                              #
# **************************************************************************** #

JC = javac
NAME = Laby.jar
MAIN = Laby.java
MANI = META-INF/MANIFEST.MF
SRC =  Cell.java \
	   Creature.java \
	   Direction.java \
	   Exit.java \
	   Hero.java \
	   Laby.java \
	   LController.java \
	   LModel.java \
	   LView.java \
	   Monster.java \
	   Nobody.java \
	   Wall.java
CLASS = $(SRC:.java=.class)


all: $(NAME)

$(NAME): $(CLASS)
	jar cvmf $(MANI) $@ $<

$(CLASS):
	cd src && \
	$(JC) $(MAIN) && \
	cp $@ ../ && \
	cd ..

clean:
	rm -f $(CLASS)

fclean: clean
	rm -f $(NAME)

re: fclean all
