.PHONY: all rocq ocaml extraction bench clean check check-c check-all \
        release-gate wc-o1-gate strict-wc-o1-gate catenable-wc-o1-gate \
        ports-wc-o1-gate wc-o1-kt4-assumptions wc-o1-kcad9-assumptions \
        deque-keystone-gate \
        catenable-refinement-check catenable-adversarial-benches \
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

wc-o1-gate:
	tools/check_wc_o1_release_gate.sh minimum

strict-wc-o1-gate:
	tools/check_wc_o1_release_gate.sh strict

catenable-wc-o1-gate:
	tools/check_wc_o1_release_gate.sh catenable

ports-wc-o1-gate:
	tools/check_wc_o1_release_gate.sh ports

# Deque keystone gate (rebuild): the UNCONDITIONAL WC O(1) theorems
# deque_wc_o1_{push,inject,pop,eject} in DequePtr/DequeKeystone.v.
# This gate checks the summit, not the frontier: it passes iff the keystone
# file builds and every Print Assumptions in it reports
# "Closed under the global context".
deque-keystone-gate:
	@dune clean --root . 2>/dev/null; true
	@echo "== Deque keystone: Print Assumptions for deque_wc_o1_* =="
	@output=$$(dune build rocq/KTDeque/DequePtr/DequeKeystone.vo --display=quiet --no-buffer 2>&1); \
	  status=$$?; \
	  if [ $$status -ne 0 ]; then \
	    printf '%s\n' "$$output"; \
	    exit $$status; \
	  fi; \
	  printf '%s\n' "$$output" | grep -c "Closed under the global context" \
	    | { read n; \
	        if [ "$$n" -eq 4 ]; then \
	          echo "OK: 4/4 keystone theorems closed under the global context"; \
	        else \
	          echo "FAIL: expected 4 closed keystone theorems, saw $$n"; \
	          exit 1; \
	        fi; }

# Gate B audit: print the axiom dependencies for each public kt4 theorem in
# rocq/KTDeque/DequePtr/PublicTheorems.v.  Expected: every theorem reports
# "Closed under the global context" (zero project-local axioms / admits).
wc-o1-kt4-assumptions:
	@dune clean --root . 2>/dev/null; true
	@echo "== Print Assumptions for the kt4 public theorem bundle =="
	@output=$$(dune build rocq/KTDeque/DequePtr/PublicTheoremsAudit.vo --display=quiet --no-buffer 2>&1); \
	  status=$$?; \
	  if [ $$status -ne 0 ]; then \
	    printf '%s\n' "$$output"; \
	    exit $$status; \
	  fi; \
	  printf '%s\n' "$$output" \
	    | grep -E "^(Closed under|Axioms:|Assumptions:|Parameters:|Sections:|Module:|Variables:)" \
	    || true
	@echo "(Each line above is the output of one Print Assumptions.)"

# Gate D audit slice: print the axiom dependencies for the Rocq Cadeque9 fast
# theorem bundle.  This is intentionally smaller than Gate B:
# it covers sequence preservation, the public boundary-element invariant,
# invariant preservation, non-empty pop/eject totality under that invariant,
# the OCaml-shape StoredMiddle9 normalizer/refill/pop/eject/concat sequence
# slice, exact OCaml pop/eject totality and weak-boundary preservation from
# the public invariant, the depth-indexed OCaml-ready and empty-or-ready
# surfaces with exact pop/eject totality, weak-boundary preservation, and
# push/inject/concat preservation for the empty-or-ready surface, exact
# pop/eject totality and weak-boundary preservation from that surface, the
# deep XBase-only invariant preserved by push/inject/concat, fuelled
# normalizers, refills, and pop/eject wrappers, the combined reachable-depth
# package built from the ready-or-empty and deep-XBase halves, and the first
# non-empty-boundary / exposed-ready constant-fuel normalization slices plus
# depth-indexed nested-middle, refill-wrapper exposure, and the T+T concat
# scheduled right-middle split / arbitrary-depth lower-bound facts, the
# bridge-middle T+T concat shape, the empty-right-middle no-wrapper case, a
# checked same-depth empty-or-ready example for the current concat shape, and a
# checked counterexample to the tempting direct-StoreBig shape.
wc-o1-kcad9-assumptions:
	@dune clean --root . 2>/dev/null; true
	@echo "== Print Assumptions for the Cadeque9 public theorem bundle =="
	@output=$$(dune build rocq/KTDeque/Cadeque9/PublicTheoremsAudit.vo --display=quiet --no-buffer 2>&1); \
	  status=$$?; \
	  if [ $$status -ne 0 ]; then \
	    printf '%s\n' "$$output"; \
	    exit $$status; \
	  fi; \
	  printf '%s\n' "$$output" \
	    | grep -E "^(Closed under|Axioms:|Assumptions:|Parameters:|Sections:|Module:|Variables:)" \
	    || true
	@echo "(Each line above is the output of one Print Assumptions.)"

catenable-refinement-check:
	$(MAKE) wc-o1-kcad9-assumptions
	dune exec ocaml/bench/kshim_qcheck.exe
	dune exec ocaml/bench/k9_qcheck.exe
	dune exec ocaml/bench/k9_depth_probe.exe
	$(MAKE) catenable-adversarial-benches
	$(MAKE) catenable-wc-o1-gate

catenable-adversarial-benches:
	dune exec --profile=release ocaml/bench/k9_concat_cost.exe
	dune exec --profile=release ocaml/bench/k9_tt_concat_stress.exe

release-gate:
	$(MAKE) wc-o1-kt4-assumptions
	dune build rocq/KTDeque ocaml
	dune runtest
	$(MAKE) -C c check
	$(MAKE) wc-o1-gate

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
