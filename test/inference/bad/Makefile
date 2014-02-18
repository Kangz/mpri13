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
	  echo -e "\e[0;31m*** Succeed when should have failed ***\e[m $<";	\
	else 							\
	  echo -e "\e[0;32m[OK]\e[m $<\n";					\
	  touch $@; 						\
	fi

clean:
	rm -f *.ml *.ko *.mle *.mls *.mlr *.mlse
