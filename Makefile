CAMLC = ocamlc
CAMLOPT = ocamlopt

all: mtt.opt

OBJECTS = \
  robdd.cmo pt.cmo ta.cmo mtt.cmo syntax.cmo parser.cmo lexer.cmo \
  main.cmo

mtt: $(OBJECTS)
	$(CAMLC) -o ta $(OBJECTS)

mtt.opt: $(OBJECTS:.cmo=.cmx)
	$(CAMLOPT) -o ta.opt $(OBJECTS:.cmo=.cmx)

include .depend

depend:
	ocamldep *.ml *.mli > .depend

clean:
	rm -f *.cm* *.o *~ lexer.ml parser.ml parser.mli 
	rm -f mtt mtt.opt

.SUFFIXES: .ml .mli .cmo .cmi .cmx

.ml.cmo:
	ocamlc -c $<

.ml.cmx:
	ocamlopt -c $<

.mli.cmi:
	ocamlc -c $<

parser.ml: parser.mly
	ocamlyacc $<
	ocamlc -c parser.mli

lexer.ml: lexer.mll
	ocamllex $<
