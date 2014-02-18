JOUJOU = ../../../src/joujou
OPTIONS =
OCAMLC = ocamlc -w -P-Y-Z

TESTS = $(shell ls *.mlt 2> /dev/null)
RUNS = $(shell ls *_run.ml 2> /dev/null)

TARGETS = $(patsubst %.mlt, %.ml, $(TESTS)) \
	  $(patsubst %.mlt, %.cmo, $(TESTS)) \
	  $(patsubst %_run.ml, %.out, $(RUNS))

all: $(TARGETS)

$(JOUJOU):
	@echo -e "\e[0;31m*** Please build $(JOUJOU) first\e[m"
	@exit 1

%.ml: %.mlt $(JOUJOU)
	@if OCAMLRUNPARAM=b $(JOUJOU) $(OPTIONS) $<; then \
	  echo -e "\e[0;32m[OK]\e[m Elaboration of $<";			\
	else						\
	  echo -e "\e[0;31m[KO]\e[m Elaboration of $<";			\
	fi

%.cmo: %.ml
	@if $(OCAMLC) -c $<; then 		\
	  echo -e "\e[0;32m[OK]\e[m Compilation of $<";		\
	else 					\
	  echo -e "\e[0;31m[KO]\e[m Compilation of $<";		\
	fi

%_run.cmo: %.cmo

%.run: %.cmo %_run.cmo
	@ $(OCAMLC) -o $@ $^ # This is our source file. It must compile.

%.out: %.run
	@ if ./$<; then 			\
	  echo -e "\e[0;32m[OK]\e[m Evaluation of $<";		\
	else					\
	  echo -e "\e[0;31m[KO]\e[m Evaluation of $<";		\
	fi
	@ touch $@

clean:
	rm -f $(TARGETS) *.cmo *.cmi *.mls *.mlse *.mle *.mlr *.out
