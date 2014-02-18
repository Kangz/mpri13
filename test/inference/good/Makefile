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
	@echo `tput setaf 1`"*** Please build $(JOUJOU) first"`tput sgr0`
	@exit 1

%.ml: %.mlt $(JOUJOU)
	@if OCAMLRUNPARAM=b $(JOUJOU) $(OPTIONS) $<; then \
	  echo `tput setaf 2`"[OK]"`tput sgr0`" Elaboration of $<";			\
	else						\
	  echo `tput setaf 1`"[KO]"`tput sgr0`" Elaboration of $<";			\
	  echo;\
	fi

%.cmo: %.ml
	@if $(OCAMLC) -c $<; then 		\
	  echo `tput setaf 2`"[OK]"`tput sgr0`" Compilation of $<";		\
	else 					\
	  echo `tput setaf 1`"[KO]"`tput sgr0`" Compilation of $<";		\
	  echo;\
	fi

%_run.cmo: %.cmo

%.run: %.cmo %_run.cmo
	@ $(OCAMLC) -o $@ $^ # This is our source file. It must compile.

%.out: %.run
	@ if ./$<; then 			\
	  echo `tput setaf 2`"[OK]"`tput sgr0`" Evaluation of $<";		\
	else					\
	  echo `tput setaf 1`"[KO]"`tput sgr0`" Evaluation of $<";		\
	  echo;\
	fi
	@ touch $@

clean:
	rm -f $(TARGETS) *.cmo *.cmi *.mls *.mlse *.mle *.mlr *.out
