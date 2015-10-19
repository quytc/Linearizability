SOURCES = globals.ml debug.ml data.ml label.ml observer.ml promise.ml \
          joinset.ml \
          info.ml constraint.ml rule.ml \
          example.ml workQueue.ml forwardAnalysis.ml \
          treiber.ml  unordered.ml  optimistic.ml  pessimistic.ml  lazyset.ml  HMset.ml  THarris.ml  MMichael.ml  Vechev.ml  \
           Vechev_CAS.ml  CCAS.ml  RDCSS.ml  Vechev_DCAS.ml  MS.ml ElimMS.ml  twolockMS.ml  DGLM.ml  HSYstack.ml  HWqueue.ml main.ml \
	      

EXEC = ../run

DOCDIR=.

OCAMLC = ocamlc.opt
OCAMLOPT = ocamlopt.opt
OCAMLDEP = ocamldep

LIBS=str.cma #unix.cma nums.cma

##############################################################

all:: .depend.input .depend $(EXEC)

opt:: .depend.input .depend $(EXEC).opt

OBJS = $(SOURCES:.ml=.cmo)
OPTOBJS = $(OBJS:.cmo=.cmx)

$(EXEC): $(OBJS) 
	$(OCAMLC) -o $@ $(LIBS) $(OBJS)

$(EXEC).opt: $(OPTOBJS)
	$(OCAMLOPT) -o $@ $(LIBS:.cma=.cmxa) $(OPTOBJS)

.SUFFIXES: .ml .mli .cmo .cmi .cmx

.ml.cmo:
	$(OCAMLC) -c $<

.mli.cmi:
	$(OCAMLC) -c $<

.ml.cmx:
	$(OCAMLOPT) -c $<

# .depend.input: Makefile
# 	@echo '--Checking Ocaml input files: '
# 	@(ls $(SOURCES) $(SOURCES:.ml=.mli) 2>/dev/null || true) > .depend.new
# 	@diff .depend.new .depend.input 2>/dev/null 1>/dev/null && \
# 	    (echo 'unchanged'; rm -f .depend.new) || \
# 	    (echo 'changed'; mv .depend.new .depend.input)

# .depend:: $(SOURCES) .depend.input
# 	@echo '--Re-building dependencies'
# 	$(OCAMLDEP) $(SOURCES) $(SOURCES:.ml=.mli) > .depend
.depend.input: Makefile
	@(ls $(SOURCES) $(SOURCES:.ml=.mli) 2>/dev/null || true) > .depend.new
	@diff .depend.new .depend.input 2>/dev/null 1>/dev/null && (rm -f .depend.new) || (mv .depend.new .depend.input)
.depend:: $(SOURCES) .depend.input
	$(OCAMLDEP) $(SOURCES) $(SOURCES:.ml=.mli) > .depend
depend: .depend

clean::
	rm -f *.cm[iox] *.o *.a *~ .*~ #*#
	rm -f $(EXEC) $(EXEC).opt #$(EXEC).debug

-include .depend

##############################################################
FILES=$(filter-out main.ml,$(SOURCES))
INTERFACES=$(FILES:.ml=.mli)
doc: $(INTERFACES) $(FILES) $(OBJS)
	ocamldoc -charset utf8 -d $(DOCDIR) -html -I . -colorize-code $(INTERFACES) $(FILES)

dist:
	echo Makefile $(SOURCES) $(SOURCES:.ml=.mli)
