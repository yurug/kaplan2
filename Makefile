.PHONY: all rocq ocaml extraction bench clean check check-c check-all \
        bench-three-way bench-canonical bench-sweep bench-adversarial bench-all

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

# Scaling sweep: vary N from 10^4 to 10^9 and emit PNG plots showing
# ns/op vs N for each (op, impl).  At n=10^9 the OCaml side runs out
# of memory; that size is C-only.  PNGs land in bench/plots/ (tracked).
# Wall-clock at the default sweep is ~10-20 minutes on a workstation.
bench-sweep:
	bench/sweep.sh

# Adversarial persistent-fork microbench: re-execute one push from a
# saved state M times.  Defeats D4's amortized analysis (every op
# pays its single-op worst-case cost = O(log N)), demonstrating the
# operational value of WC O(1).  Wall-clock < 1 minute.
bench-adversarial:
	bench/adversarial.sh

bench-all: bench-three-way bench-canonical bench-adversarial

clean:
	dune clean
	$(MAKE) -C c clean
