CAMLC = ocamlc
CAMLOPT = ocamlopt

all: ta.opt

OBJECTS = \
  robdd.cmo pt.cmo ta.cmo mtt.cmo syntax.cmo parser.cmo lexer.cmo \
  main.cmo

ta: $(OBJECTS)
	$(CAMLC) -o ta $(OBJECTS)

ta.opt: $(OBJECTS:.cmo=.cmx)
	$(CAMLOPT) -o ta.opt $(OBJECTS:.cmo=.cmx)

include .depend

depend:
	ocamldep *.ml *.mli > .depend

clean:
	rm -f *.cm* *.o *~

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
