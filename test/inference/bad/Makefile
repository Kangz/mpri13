JOUJOU = ../../../src/joujou
OPTIONS =
OCAMLC = ocamlc -w -P-Y-Z

TESTS = $(shell ls *.mlt)

all: $(patsubst %.mlt, %.ko, $(TESTS))

$(JOUJOU):
	@echo -e "\e[0;31m*** Please build $(JOUJOU) first\e[m"
	@exit 1

%.ko: %.mlt $(JOUJOU)
	@if OCAMLRUNPARAM=b $(JOUJOU) $(OPTIONS) $<;		\
	then							\
	  echo `tput setaf 2`"*** Succeed when should have failed ***"`tput sgr0` " $<";	\
	else 							\
	  echo `tput setaf 2`"[OK]`tput sgr0` $<\n";					\
	  echo;\
	  touch $@; 						\
	fi

clean:
	rm -f *.ml *.ko *.mle *.mls *.mlr *.mlse
