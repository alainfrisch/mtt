CAMLC = ocamlc
CAMLOPT = ocamlopt

all: mtt.opt

OBJECTS = \
  robdd.cmo pt.cmo ta.cmo mtt.cmo regexp.cmo syntax.cmo parser.cmo lexer.cmo \
  main.cmo

mtt: $(OBJECTS)
	$(CAMLC) -o mtt $(OBJECTS)

mtt.opt: $(OBJECTS:.cmo=.cmx)
	$(CAMLOPT) -o mtt.opt $(OBJECTS:.cmo=.cmx)

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

PACKAGE=mtt-0.2
PACK_FILES=\
 Makefile .depend *.ml *.mli *.mly *.mll *.mtt \
 CHANGES LICENSE README SPECIF

package:
	rm -Rf $(PACKAGE)
	mkdir $(PACKAGE)
	cp $(PACK_FILES) $(PACKAGE)
	tar czf $(PACKAGE).tar.gz $(PACKAGE)
copy:
	scp $(PACKAGE).tar.gz README SPECIF \
          buzet.inria.fr:public_html/mtt
