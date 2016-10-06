#
# Mettre la liste des fichiers .ml, .mly, .mll et .mli
# constituant le projet. Si un fichier b.ml dépend d'un fichier
# a.ml, a.ml doit se trouver avant dans la liste.
#

SOURCES = ast.mli parser.mly lexer.mll interpreter.ml \
	compiler.ml main.ml	

# Nom du binaire

EXEC = compilo

# Nom de l'utilitaire MARS

MARS_EXEC = Mars4_5.jar

#######################################################################
# Partie générique, ne pas modifier.
#######################################################################




# Compilateurs

CAMLC = ocamlc -g -annot
CAMLOPT = ocamlopt
CAMLDEP = ocamldep
CAMLLEX = ocamllex
CAMLYACC = menhir --infer

# Interprète

INTERPRET = ./$(EXEC) -i

# Sources

SRC_MLL = $(filter %.mll, $(SOURCES))
SRC_MLY = $(filter %.mly, $(SOURCES))
SMLIY = $(SOURCES:.mly=.ml)
SMLIYL = $(SMLIY:.mll=.ml)
SMLYL = $(filter %.ml,$(SMLIYL))
OBJS = $(SMLYL:.ml=.cmo)
OPTOBJS = $(OBJS:.cmo=.cmx)

# Tests

MARS = java -jar $(MARS_EXEC) nc


# Cibles

all: depend $(EXEC)
	@echo -e "\033[32mVous pouvez utiliser make test [0 ou 1] file1 file2 ...\033[0m"

opt: depend $(EXEC).opt


.SUFFIXES: .ml .mli .cmo .cmi .cmx .mll .mly .asm

$(EXEC): $(OBJS)
	$(CAMLC) $(CUSTOM) -o $(EXEC) $(OBJS)

$(EXEC).opt: $(OPTOBJS)
	$(CAMLOPT) -o $(EXEC) $(OPTOBJS)

parser.cmo : ast.cmi parser.cmi
parser.cmx : ast.cmi parser.cmi
parser.cmi : ast.cmi
parser.ml parser.mli: ast.cmi

.ml.cmo:
	$(CAMLC) -c $<

.mli.cmi:
	$(CAMLC) -c $<

.ml.cmx:
	$(CAMLOPT) -c $<

.mll.cmo:
	$(CAMLLEX) $<
	$(CAMLC) -c $*.ml

.mll.cmx:
	$(CAMLLEX) $<
	$(CAMLOPT) -c $*.ml

.mly.cmo:
	$(CAMLYACC) $<
	$(CAMLC) -c $*.mli
	$(CAMLC) -c $*.ml

.mly.cmx:
	$(CAMLYACC) $<
	$(CAMLOPT) -c $*.mli
	$(CAMLOPT) -c $*.ml

.mly.cmi:
	$(CAMLYACC) $<
	$(CAMLC) -c $*.mli

.mll.ml:
	$(CAMLLEX) $<

.mly.ml:
	$(CAMLYACC) $<

.ml.asm: 
	./$(EXEC) $<

test: all
	@./testall.sh $(filter-out $@,$(MAKECMDGOALS))

clean:
	rm -f *.cm[iox] *~ .*~ *.o *.annot *.conflicts *.output
	rm -f $(SRC_MLL:.mll=.ml) $(SRC_MLY:.mly=.ml) $(SRC_MLY:.mly=.mli)
	rm -f $(TEST_ASM_ALL)
	rm -f $(EXEC)
	rm -f $(EXEC).opt

clean_test_all:
	rm -f $(TEST_ASM_ALL)

clean_test:
	rm -f $(TEST_ASM)

re: clean all

coffee:
	@clear
	@echo ""
	@echo "                   ("
	@echo "                         )     ("
	@echo "               ___...(-------)-....___"
	@echo '           .-""       )    (          ""-.'
	@echo "      .-''''|-._             )         _.-|"
	@echo '     /  .--.|   `""---...........---""`   |'
	@echo "    /  /    |                             |"
	@echo "    |  |    |                             |"
	@echo "     \  \   |                             |"
	@echo "      '\ '\ |                             |"
	@echo "        '\ '|                             |"
	@echo "        _/ /\                             /"
	@echo "       (__/  \                           /"
	@echo '    _..---""` \                         /`""---.._'
	@echo " .-'           \                       /          '-."
	@echo ":               '-.__             __.-'              :"
	@echo ':                  ) ""---...---"" (                :'
	@echo "\'._                '"--...___...--"'              _.'"
	@echo '   \""--..__                              __..--""/'
	@echo "     '._     """----.....______.....----"""         _.'"
	@echo '         ""--..,,_____            _____,,..--"""'''
	@echo '                      """------"""'
	@sleep 0.5
	@clear
	@echo ""
	@echo "                 ("
	@echo "                      )      ("
	@echo "               ___..(.------)--....___"
	@echo '           .-""       )   (           ""-.'
	@echo "      .-''''|-._      (       )        _.-|"
	@echo '     /  .--.|   `""---...........---""`   |'
	@echo "    /  /    |                             |"
	@echo "    |  |    |                             |"
	@echo "     \  \   |                             |"
	@echo "      '\ '\ |                             |"
	@echo "        '\ '|                             |"
	@echo "        _/ /\                             /"
	@echo "       (__/  \                           /"
	@echo '    _..---""` \                         /`""---.._'
	@echo " .-'           \                       /          '-."
	@echo ":               '-.__             __.-'              :"
	@echo ':                  ) ""---...---"" (                :'
	@echo "\'._                '"--...___...--"'              _.'"
	@echo '   \""--..__                              __..--""/'
	@echo "     '._     """----.....______.....----"""         _.'"
	@echo '         ""--..,,_____            _____,,..--"""'''
	@echo '                      """------"""'
	@sleep 0.5
	@clear
	@echo ""
	@echo "               ("
	@echo "                      )     ("
	@echo "               ___..(.------)--....___"
	@echo '           .-""      )    (           ""-.'
	@echo "      .-''''|-._      (       )        _.-|"
	@echo '     /  .--.|   `""---...........---""`   |'
	@echo "    /  /    |                             |"
	@echo "    |  |    |                             |"
	@echo "     \  \   |                             |"
	@echo "      '\ '\ |                             |"
	@echo "        '\ '|                             |"
	@echo "        _/ /\                             /"
	@echo "       (__/  \                           /"
	@echo '    _..---""` \                         /`""---.._'
	@echo " .-'           \                       /          '-."
	@echo ":               '-.__             __.-'              :"
	@echo ':                  ) ""---...---"" (                :'
	@echo "\'._                '"--...___...--"'              _.'"
	@echo '   \""--..__                              __..--""/'
	@echo "     '._     """----.....______.....----"""         _.'"
	@echo '         ""--..,,_____            _____,,..--"""'''
	@echo '                      """------"""'
	@sleep 0.5
	@clear
	@echo ""
	@echo "             (         ) "
	@echo "                  )        ("
	@echo "               ___)...----)----....___"
	@echo '           .-""      )    (           ""-.'
	@echo "      .-''''|-._      (       )        _.-|"
	@echo '     /  .--.|   `""---...........---""`   |'
	@echo "    /  /    |                             |"
	@echo "    |  |    |                             |"
	@echo "     \  \   |                             |"
	@echo "      '\ '\ |                             |"
	@echo "        '\ '|                             |"
	@echo "        _/ /\                             /"
	@echo "       (__/  \                           /"
	@echo '    _..---""` \                         /`""---.._'
	@echo " .-'           \                       /          '-."
	@echo ":               '-.__             __.-'              :"
	@echo ':                  ) ""---...---"" (                :'
	@echo "\'._                '"--...___...--"'              _.'"
	@echo '   \""--..__                              __..--""/'
	@echo "     '._     """----.....______.....----"""         _.'"
	@echo '         ""--..,,_____            _____,,..--"""'''
	@echo ''

depend: $(SMLIY)
	$(CAMLDEP) $(SMLIY) $(SMLIY:.mly:.mli) > .depend

-include .depend
