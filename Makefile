.PHONY: all rocq ocaml extraction bench clean check check-c check-all \
        bench-three-way bench-canonical bench-all

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

# Top-level reproducible benchmarks.  See bench/README.md for methodology.
#   bench-three-way  — our C / our OCaml / Viennot OCaml at n=1M
#   bench-canonical  — verified ktdeque vs Viennot / our handwritten / list ref,
#                      across a workload battery (steady, adversarial, fork)
#   bench-all        — runs both
bench-three-way:
	bench/three-way.sh

bench-canonical:
	bench/canonical.sh

bench-all: bench-three-way bench-canonical

clean:
	dune clean
	$(MAKE) -C c clean
