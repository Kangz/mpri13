JOUJOU = ../../../src/joujou
OPTIONS =
OCAMLC = ocamlc -w -P-Y-Z

TESTS = $(shell ls *.mle)

all: $(patsubst %.mle, %.ko, $(TESTS))

$(JOUJOU):
	@echo `tput setaf 1`"*** Please build $(JOUJOU) first"`tput sgr0`
	@exit 1

%.ko: %.mle $(JOUJOU)
	@if OCAMLRUNPARAM=b $(JOUJOU) $(OPTIONS) $<;		\
	then							\
	  echo `tput setaf 1`"*** Succeed when should have failed ***"`tput sgr0` $<;	\
	  exit 1; 						\
	else 							\
	  echo `tput setaf 2`"[OK]"`tput sgr0` $<;					\
	  echo; \
	  touch $@; 						\
	fi

clean:
	rm -f *.ml *.ko *.mlr *.mls *.mlse
