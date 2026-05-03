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
#   make check-all  — full matrix incl. ASan, UBSan, TSan, fuzz, differential
#                     (~30 sec wall-clock); the differential test depends on
#                     the OCaml extraction being built.
check check-c:
	$(MAKE) -C c check

check-all:
	dune build ocaml/extracted/diff_workload.exe
	$(MAKE) -C c check-all

clean:
	dune clean
	$(MAKE) -C c clean
