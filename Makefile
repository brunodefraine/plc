OCAML=ocaml
OCAMLC=ocamlc.opt
OCAMLOPT=ocamlopt.opt
CAMLP4=camlp4
INCLUDES=
P4O=OCamlRevisedParser OCamlParser
P4GRAM=GrammarParser
P4QUOT=QuotationCommon OCamlRevisedQuotationExpander
P4DUMP=OCamlAstDumper
P4PR=OCamlPrinter
P4AUTO=AutoPrinter
PAS=
PRS=
PPS=$(foreach PA,$(PAS),-parser Camlp4$(PA)) $(foreach PR,$(PRS),-printer Camlp4$(PR))
PPFLAGS=$(if $(strip $(PPS)),-pp '$(CAMLP4) $(PPS) -loc _loc')
OCAMLFLAGS=-dtypes $(INCLUDES) $(PPFLAGS)
CPP=cpp -C -traditional-cpp -xc

demo: demo.cmo demo_driver.ml
	$(OCAML) demo.cmo demo_driver.ml

nqueens_driver.cmo: nqueens.cmo
nqueens_driver.cmx: nqueens.cmx
nqueens.opt: nqueens.cmx nqueens_driver.cmx
	$(OCAMLOPT) -o $@ $+

nqueens.pl: nqueens.cpp
	$(CPP) -P -o $@ $<

nqueens.m: nqueens.cpp
	$(CPP) -DMERCURY -P -o $@ $<

nqueens_mercury: nqueens.m
	mmc --make nqueens_mercury

.PHONY: demo

# Dependencies

ast.cmo ast.cmx: override INCLUDES=
ast.cmo ast.cmx: override PAS=
ast.cmo ast.cmx: override PRS=
env.cmi env.cmo env.cmx: override INCLUDES=
env.cmi env.cmo env.cmx: override PAS=
env.cmi env.cmo env.cmx: override PRS=
env.cmo: env.cmi
env.cmx: env.cmi
version.cmi version.cmo version.cmx: override INCLUDES=
version.cmi version.cmo version.cmx: override PAS=
version.cmi version.cmo version.cmx: override PRS=
version.cmo: version.cmi
version.cmx: version.cmi
names.cmo names.cmx: override INCLUDES=
names.cmo names.cmx: override PAS=
names.cmo names.cmx: override PRS=
names.cmo: version.cmo
names.cmx: version.cmx
parser.cmo parser.cmx: override INCLUDES+=-I +camlp4
parser.cmo parser.cmx: override PAS=$(P4O) $(P4GRAM)
parser.cmo parser.cmx: override PRS=$(P4DUMP)
parser.cmo: ast.cmo names.cmo
parser.cmx: ast.cmx names.cmx
mlgen.cmo mlgen.cmx: override INCLUDES+=-I +camlp4
mlgen.cmo mlgen.cmx: override PAS=$(P4O) $(P4QUOT)
mlgen.cmo mlgen.cmx: override PRS=$(P4DUMP)
translate.cmo translate.cmx: override INCLUDES+=-I +camlp4
translate.cmo translate.cmx: override PAS=$(P4O) $(P4QUOT)
translate.cmo translate.cmx: override PRS=$(P4DUMP)
translate.cmo: ast.cmo version.cmo names.cmo env.cmo mlgen.cmo
translate.cmx: ast.cmx version.cmx names.cmx env.cmx mlgen.cmx
fe.cmo fe.cmx: override INCLUDES+=-I +camlp4
fe.cmo fe.cmx: override PAS=$(P4O) $(P4GRAM)
fe.cmo fe.cmx: override PRS=$(P4DUMP)
fe.cmo: parser.cmo translate.cmo ast.cmo
fe.cmx: parser.cmx translate.cmx ast.cmx

# Rules

%.cmi: %.mli
	$(OCAMLC) -c $(OCAMLFLAGS) $<

%.cmo %.cmi: %.ml
	$(OCAMLC) -c $(OCAMLFLAGS) $<

%.cmx %.cmi: %.ml
	$(OCAMLOPT) -c $(OCAMLFLAGS) $<

plc.opt: ast.cmx version.cmx names.cmx env.cmx mlgen.cmx translate.cmx parser.cmx fe.cmx
	$(OCAMLOPT) -o $@ -I +camlp4 camlp4lib.cmxa $+ unix.cmxa Camlp4Printers/Camlp4$(P4AUTO).cmx Camlp4Bin.cmx
	strip $@

%.output: %.pl plc.opt
	./plc.opt -impl $<

%.cmo %.cmi: %.pl plc.opt
	$(OCAMLC) -c $(OCAMLFLAGS) -pp './plc.opt -impl' -impl $<

%.cmx %.cmi: %.pl plc.opt
	$(OCAMLOPT) -c $(OCAMLFLAGS) -pp './plc.opt -impl' -impl $<

