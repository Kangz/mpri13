JOUJOU = ../../../src/joujou
OPTIONS =
OCAMLC = ocamlc -w -P-Y-Z

TESTS = $(shell ls *.mle 2> /dev/null)
RUNS = $(shell ls *_run.ml 2> /dev/null)

TARGETS = $(patsubst %.mle, %.ml, $(TESTS)) \
	  $(patsubst %.mle, %.cmo, $(TESTS)) \
	  $(patsubst %_run.ml, %.out, $(RUNS))

all: $(TARGETS)

$(JOUJOU):
	@echo -e "\e[0;31m*** Please build $(JOUJOU) first\e[m"
	@exit 1

%.ml: %.mle $(JOUJOU)
	@if OCAMLRUNPARAM=b $(JOUJOU) $(OPTIONS) $<; then \
	  echo -e "\e[0;32m[OK] Elaboration of $<\e[m";			\
	else						\
	  echo -e "\e[0;31m[KO] Elaboration of $<\e[m";			\
	fi

%.cmo: %.ml
	@ if $(OCAMLC) -c $<; then 		\
	  echo -e "\e[0;32m[OK] Compilation of $<\e[m";		\
	else 					\
	  echo -e "\e[0;31m[KO] Compilation of $<\e[m";		\
	fi

%_run.cmo: %.cmo

%.run: %.cmo %_run.cmo
	@ $(OCAMLC) -o $@ $^ # This is our source file. It must compile.

%.out: %.run
	@ if ./$<; then 			\
	  echo -e "\e[0;32m[OK] Evaluation of $<\e[m";		\
	else					\
	  echo -e "\e[0;31m[KO] Evaluation of $<\e[m";		\
	fi
	@ touch $@

clean:
	rm -f $(TARGETS) *.cmo *.cmi *.mls *.mlr *.out *.mlse
