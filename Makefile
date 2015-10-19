PROPERTY=linearizability
EX=treiber

# Checking for NullPointer and Dangling pointer dereferencing, and Cycle creation
# Not checking for free cells dereferencing (-f)
ARGS=-n -d

DIST=dist.tar.gz

all:
	@make -C src
	./run -p $(PROPERTY) -e $(EX) $(ARGS)

opt:
	@make -C src opt
	./run.opt -p $(PROPERTY) -e $(EX) $(ARGS)

opt.noassert:
	@make -C src opt OCAMLOPT:="ocamlopt.opt -noassert"
	./run.opt -p $(PROPERTY) -e $(EX) $(ARGS)

debug: clean
	@make -C src OCAMLC:="ocamlc -g"
	ocamldebug run -p $(PROPERTY) -e $(EX) $(ARGS)

profile:clean
	@make -C src OCAMLC:="ocamlcp -p a"
	./run -p $(PROPERTY) -e $(EX) $(ARGS)
#	gprof run

profile.opt:clean
	@make -C src opt OCAMLOPT:="ocamloptp -p"
	./run.opt -p $(PROPERTY) -e $(EX) $(ARGS)
	gprof run.opt > profile.txt

profile.opt.noassert:clean
	@make -C src opt OCAMLOPT:="ocamloptp -p -noassert"
	./run.opt -p $(PROPERTY) -e $(EX) $(ARGS)
#	gprof run.opt > profile.txt

clean:
	@make -s -C src clean
	@-rm -rf tmp
	@find . -type f -iname '*~' -exec rm {} \;

cleanall: clean
	@-rm -f profile.txt gmon.out ocamlprof.dump
	@-rm -rf results.txt bugs.txt
	@-rm -rf doc
	@-rm -f $(DIST)
	@echo "Cleaning done"

.PHONY: doc
doc:
	@-rm -rf doc
	@mkdir -p doc
	@echo Creating the doc \(see the "\033[4m"doc"[0m" directory\)
	@make -s -C src doc DOCDIR:="../doc"

$(DIST):cleanall
	@echo Creating the distribution \(in "\033[1m"$(DIST)"[0m"\)
	@make -s -C src .depend.input
	@ls CVS/* > exclude
	@ls src/CVS/* >> exclude
	@sed 's/^/src\//' src/.depend.input | xargs tar -zcf $(DIST) -X exclude --exclude="CVS" --exclude="src/CVS" Makefile src/Makefile
	@rm exclude

dist:$(DIST)

senddist:$(DIST)
	@echo Sending the whole shebang to "\033[1m"sarka.fit.vutbr.cz"[0m"
	@scp -q $(DIST) daz@sarka.fit.vutbr.cz:./lfds/.

fetch:
	@echo Fetching the results from "\033[1m"sarka.fit.vutbr.cz"[0m"
	@-scp -q daz@sarka.fit.vutbr.cz:./lfds/results.txt .
	@-scp -q daz@sarka.fit.vutbr.cz:./lfds/bugs.txt .
	@-scp -q daz@sarka.fit.vutbr.cz:./lfds/shapes.txt .

examples:
	@make -s -C src opt OCAMLOPT:="ocamlopt.opt -noassert" OCAMLC:="ocamlc.opt -noassert"
	@rm -f results.txt
	@touch results.txt
	@echo "Experimental results for Concurrent Shape Analysis"
	@echo "...Coarse Stack"
	@./run.opt -e coarsestack -p stack_all $(ARGS) >> results.txt
	@echo "...Coarse Stack, no GC"
	@./run.opt -e coarsestacknogc -p stack_all $(ARGS) >> results.txt
	@echo "...Coarse Queue"
	@./run.opt -e coarsequeue -p queue_all $(ARGS) >> results.txt
	@echo "...Coarse Queue, no GC"
	@./run.opt -e coarsequeuenogc -p queue_all $(ARGS) >> results.txt
	@echo "...Two-Locks queue"
	@./run.opt -e twolocksqueue -p queue_all $(ARGS) >> results.txt
	@echo "...Two-Locks Queue, no GC"
	@./run.opt -e twolocksqueuenogc -p queue_all $(ARGS) >> results.txt
	@echo "...Priority Queue"
	@./run.opt -e coarseprioqueuebuckets -p prioqueue $(ARGS) >> results.txt
	@./run.opt -e coarseprioqueuelistbased -p prioqueue $(ARGS) >> results.txt
	@./run.opt -e bucketlocksprioqueue -p prioqueue $(ARGS) >> results.txt
	@echo "...Treiber"
	@./run.opt -e treiber -p stack_all $(ARGS) >> results.txt
	@echo "...Treiber noGC"
	@./run.opt -e treibernogc -p stack_all $(ARGS) >> results.txt
	@echo "...M&S"
	@./run.opt -e ms -p queue_all $(ARGS) >> results.txt
	@echo "...M&S no GC"
	@./run.opt -e msnogc -p queue_all $(ARGS) >> results.txt

shapes:
	@make -s -C src opt OCAMLOPT:="ocamlopt.opt -noassert" OCAMLC:="ocamlc.opt -noassert"
	@rm -f shapes.txt
	@touch shapes.txt
	@echo "Experimental results for Concurrent Shape Analysis - Memory safety"
	@echo "...Coarse Stack"
	@./run.opt -e coarsestack -p shape $(ARGS) >> shapes.txt
	@echo "...Coarse Stack, no GC"
	@./run.opt -e coarsestacknogc -p shape $(ARGS) >> shapes.txt
	@echo "...Coarse Queue"
	@./run.opt -e coarsequeue -p shape $(ARGS) >> shapes.txt
	@echo "...Coarse Queue, no GC"
	@./run.opt -e coarsequeuenogc -p shape $(ARGS) >> shapes.txt
	@echo "...Two-Locks queue"
	@./run.opt -e twolocksqueue -p shape $(ARGS) >> shapes.txt
	@echo "...Two-Locks Queue, no GC"
	@./run.opt -e twolocksqueuenogc -p shape $(ARGS) >> shapes.txt
	@echo "...Priority Queue"
	@./run.opt -e coarseprioqueuebuckets -p shapeprio $(ARGS) >> shapes.txt
	@./run.opt -e coarseprioqueuelistbased -p shapeprio $(ARGS) >> shapes.txt
	@./run.opt -e bucketlocksprioqueue -p shapeprio $(ARGS) >> shapes.txt
	@echo "...Treiber"
	@./run.opt -e treiber -p shape $(ARGS) >> shapes.txt
	@echo "...Treiber noGC"
	@./run.opt -e treibernogc -p shape $(ARGS) >> shapes.txt
	@echo "...M&S"
	@./run.opt -e ms -p shape $(ARGS) >> shapes.txt
	@echo "...M&S no GC"
	@./run.opt -e msnogc -p shape $(ARGS) >> shapes.txt

bugs:
	@make -s -C src opt OCAMLOPT:="ocamlopt.opt -noassert" OCAMLC:="ocamlc.opt -noassert"
	@rm -f bugs.txt
	@touch bugs.txt
	@echo "Experimental results for Concurrent Shape Analysis (with intentional bugs)"
	@./run.opt -e treiber -p queue -n -d >> bugs.txt
	@./run.opt -e treibernogc -p shape -f >> bugs.txt
	@./run.opt -e treibernogc -p queue -n -d >> bugs.txt
	@./run.opt -e ms -p stack -n -d >> bugs.txt
	@./run.opt -e bug_2lockQcommitunlock -p queue_all -n -d -c >> bugs.txt
	@./run.opt -e bug_treiberwrongdata -p loss -n -d >> bugs.txt
	@./run.opt -e bug_mscommitempty -p loss -d -n >> bugs.txt
	@./run.opt -e bug_msswap -p queue_all >> bugs.txt
	@./run.opt -e bug_msswap -p queue_all -n -d -c >> bugs.txt
	@./run.opt -e bug_treibernocounter -p loss >> bugs.txt
	@./run.opt -e bug_treibernocounter -p loss -n -d -c >> bugs.txt
	@./run.opt -e bug_msnocounter -p loss >> bugs.txt
	@./run.opt -e bug_msnocounter -p loss -n -d -c >> bugs.txt

# examples:
# 	@make -s -C src opt OCAMLOPT:="ocamlopt.opt -noassert" OCAMLC:="ocamlc.opt -noassert"
# 	@rm -f results.txt
# 	@touch results.txt
# 	@echo "Experimental results for Concurrent Shape Analysis"
# 	@echo "...Coarse Stack"
# 	@./run.opt -e coarsestack -p stack $(ARGS) >> results.txt
# 	@./run.opt -e coarsestack -p loss $(ARGS) >> results.txt
# 	@./run.opt -e coarsestack -p creation $(ARGS) >> results.txt
# 	@./run.opt -e coarsestack -p duplication $(ARGS) >> results.txt
# 	@echo "...Coarse Stack, no GC"
# 	@./run.opt -e coarsestacknogc -p stack $(ARGS) >> results.txt
# 	@./run.opt -e coarsestacknogc -p loss $(ARGS) >> results.txt
# 	@./run.opt -e coarsestacknogc -p creation $(ARGS) >> results.txt
# 	@./run.opt -e coarsestacknogc -p duplication $(ARGS) >> results.txt
# 	@echo "...Coarse Queue"
# 	@./run.opt -e coarsequeue -p queue $(ARGS) >> results.txt
# 	@./run.opt -e coarsequeue -p loss $(ARGS) >> results.txt
# 	@./run.opt -e coarsequeue -p creation $(ARGS) >> results.txt
# 	@./run.opt -e coarsequeue -p duplication $(ARGS) >> results.txt
# 	@echo "...Coarse Queue, no GC"
# 	@./run.opt -e coarsequeuenogc -p queue $(ARGS) >> results.txt
# 	@./run.opt -e coarsequeuenogc -p loss $(ARGS) >> results.txt
# 	@./run.opt -e coarsequeuenogc -p creation $(ARGS) >> results.txt
# 	@./run.opt -e coarsequeuenogc -p duplication $(ARGS) >> results.txt
# 	@echo "...Two-Locks queue"
# 	@./run.opt -e twolocksqueue -p queue $(ARGS) >> results.txt
# 	@./run.opt -e twolocksqueue -p loss $(ARGS) >> results.txt
# 	@./run.opt -e twolocksqueue -p creation $(ARGS) >> results.txt
# 	@./run.opt -e twolocksqueue -p duplication $(ARGS) >> results.txt
# 	@echo "...Two-Locks Queue, no GC"
# 	@./run.opt -e twolocksqueuenogc -p queue $(ARGS) >> results.txt
# 	@./run.opt -e twolocksqueuenogc -p loss $(ARGS) >> results.txt
# 	@./run.opt -e twolocksqueuenogc -p creation $(ARGS) >> results.txt
# 	@./run.opt -e twolocksqueuenogc -p duplication $(ARGS) >> results.txt
# 	@echo "...Priority Queue"
# 	@./run.opt -e coarseprioqueuebuckets -p prioqueue $(ARGS) >> results.txt
# 	@./run.opt -e coarseprioqueuelistbased -p prioqueue $(ARGS) >> results.txt
# 	@./run.opt -e bucketlocksprioqueue -p prioqueue $(ARGS) >> results.txt
# 	@echo "...Treiber"
# 	@./run.opt -e treiber -p stack $(ARGS) >> results.txt
# 	@./run.opt -e treiber -p loss $(ARGS) >> results.txt
# 	@./run.opt -e treiber -p creation $(ARGS) >> results.txt
# 	@./run.opt -e treiber -p duplication $(ARGS) >> results.txt
# 	@echo "...Treiber noGC"
# 	@./run.opt -e treibernogc -p stack $(ARGS) >> results.txt
# 	@./run.opt -e treibernogc -p loss $(ARGS) >> results.txt
# 	@./run.opt -e treibernogc -p creation $(ARGS) >> results.txt
# 	@./run.opt -e treibernogc -p duplication $(ARGS) >> results.txt
# 	@echo "...M&S"
# 	@./run.opt -e ms -p queue $(ARGS) >> results.txt
# 	@./run.opt -e ms -p loss $(ARGS) >> results.txt
# 	@./run.opt -e ms -p creation $(ARGS) >> results.txt
# 	@./run.opt -e ms -p duplication $(ARGS) >> results.txt
# 	@echo "...M&S no GC"
# 	@./run.opt -e msnogc -p queue $(ARGS) >> results.txt
# 	@./run.opt -e msnogc -p loss $(ARGS) >> results.txt
# 	@./run.opt -e msnogc -p creation $(ARGS) >> results.txt
# 	@./run.opt -e msnogc -p duplication $(ARGS) >> results.txt

