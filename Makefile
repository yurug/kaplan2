.PHONY: all rocq ocaml extraction bench clean check check-c check-all

all: rocq

rocq:
	dune build rocq/KTDeque

ocaml:
	dune build ocaml

extraction:
	dune build rocq/KTDeque/Extract

bench:
	dune build ocaml/bench

# C-side correctness suite.  See c/Makefile for individual targets.
#   make check      — fast (test, test_debug, wc_test, threads)
#   make check-c    — equivalent to `make -C c check`
#   make check-all  — full matrix: static analysis + ASan + UBSan + TSan +
#                     1000-seed fuzz + 32-trace C↔OCaml differential
#                     (mix + deep cascade) + 200×64 persistence stress
#                     (~45 sec wall-clock).  The differential layers
#                     depend on the OCaml extraction binary, which this
#                     target builds first.
check check-c:
	$(MAKE) -C c check

check-all:
	dune build ocaml/extracted/diff_workload.exe
	$(MAKE) -C c check-all

clean:
	dune clean
	$(MAKE) -C c clean
