.PHONY: all pretty-timed test coqdoc clean depgraphdoc

all:
	@$(MAKE) -C theories
	@dune build

pretty-timed:
	@$(MAKE) pretty-timed -C theories
	@dune build

# For CI, only log assumption infos, but do o
pretty-timed-with-check:
# 	" :$$" matches axiom names and "^  \S" matches axiom contents
	@$(MAKE) pretty-timed -C theories | tee ./theories.log | grep -vE 'Closed under the global context|Axioms:|^  \S| :$$|<<<'
	@dune build

coqdoc:
	@${MAKE} coqdoc -C theories

depgraphdoc:
	@$(MAKE) depgraphdoc -C theories

clean:
	@$(MAKE) clean -C theories
	@dune clean
	@echo "Cleaning finished."
