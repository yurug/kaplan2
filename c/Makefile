# =====================================================================
# Build / install / test for the kaplan2 KT-deque C library.
#
#   Source layout:
#     include/    public header (ktdeque.h)
#     src/        production source (ktdeque_dequeptr.c)
#     tests/      correctness + fuzz drivers
#     benches/    microbenchmarks
#     experiments/ profile/hypothesis tests (not built by default)
#
#   Common targets:
#     make                build library + tests + bench + fuzz drivers
#     make check          fast correctness suite
#     make check-all      full matrix (sanitizers + fuzz + diff + ...)
#     make install        install libktdeque.a + header + .pc file
#     make clean          remove all build artifacts
#
# =====================================================================

CC      ?= gcc
PREFIX  ?= /usr/local
INCDIR  := include
SRCDIR  := src
TESTDIR := tests
BENCHDIR:= benches

KT_C_SRC ?= $(SRCDIR)/ktdeque_dequeptr.c
KT_HDR   := $(INCDIR)/ktdeque.h
KT_CAD_SRC ?= $(SRCDIR)/ktcadeque.c
KT_CAD_HDR := $(INCDIR)/ktcadeque.h
# Catenable (§6) layer is built on top of the §4 deque source.
KT_ALL_SRC := $(KT_C_SRC) $(KT_CAD_SRC)
KT_ALL_HDR := $(KT_HDR) $(KT_CAD_HDR)
LIBNAME  := ktdeque
LIBFILE  := lib$(LIBNAME).a

CFLAGS_COMMON = -Wall -Wextra -std=c11 -D_POSIX_C_SOURCE=199310L -I$(INCDIR)
CFLAGS  ?= -O3 -funroll-loops -finline-functions -fomit-frame-pointer -DNDEBUG $(CFLAGS_COMMON)
LDFLAGS ?=

# Sanitizer flag groups.
SAN_ASAN  = -fsanitize=address,undefined -fno-omit-frame-pointer
SAN_TSAN  = -fsanitize=thread -fno-omit-frame-pointer
CFLAGS_DEBUG = -O2 -g -UNDEBUG $(CFLAGS_COMMON)
CFLAGS_SAN   = -O1 -g -DNDEBUG $(CFLAGS_COMMON)

.PHONY: all clean lib install uninstall \
        run-test run-test-debug run-bench run-wc \
        run-fuzz run-fuzz-cadeque run-fuzz-cadeque-afl run-diff run-diff-deep run-diff-multi run-threads \
        check check-asan check-tsan check-fuzz \
        check-diff check-diff-deep check-diff-multi check-static check-fuzz-cadeque \
        check-persistence-stress check-all

# Default goal: library + tests + bench.
all: lib test test_debug bench wc_test fuzz diff_workload test_threads test_persistence_stress cadeque_test diff_cadeque fuzz_cadeque

# ---------------------------------------------------------------------
# Library archive — linkable, installable.
# ---------------------------------------------------------------------

lib: $(LIBFILE)

# The installed archive bundles BOTH the §4 deque and the §6 catenable
# deque, so kt_* and kc_* are linkable from one -lktdeque.
$(LIBFILE): ktdeque.o ktcadeque.o
	$(AR) rcs $@ $^

ktdeque.o: $(KT_C_SRC) $(KT_HDR)
	$(CC) $(CFLAGS) -c -o $@ $(KT_C_SRC)

ktcadeque.o: $(KT_CAD_SRC) $(KT_ALL_HDR)
	$(CC) $(CFLAGS) -c -o $@ $(KT_CAD_SRC)

# ---------------------------------------------------------------------
# Test / bench / fuzz drivers — each rebuilt with the appropriate
# instrumentation (sanitizers, debug, etc.).
# ---------------------------------------------------------------------

test: $(KT_C_SRC) $(TESTDIR)/test.c $(KT_HDR)
	$(CC) $(CFLAGS) -o $@ $(KT_C_SRC) $(TESTDIR)/test.c $(LDFLAGS)

# test_debug: -UNDEBUG so green_of_red regularity asserts execute.
test_debug: $(KT_C_SRC) $(TESTDIR)/test.c $(KT_HDR)
	$(CC) $(CFLAGS_DEBUG) -o $@ $(KT_C_SRC) $(TESTDIR)/test.c $(LDFLAGS)

bench: $(KT_C_SRC) $(BENCHDIR)/bench.c $(KT_HDR)
	$(CC) $(CFLAGS) -o $@ $(KT_C_SRC) $(BENCHDIR)/bench.c $(LDFLAGS)

# Persistent-fork microbench — emits CSV "C,<depth>,<size>,<ns_per_op>"
# rows, consumed by bench/adversarial.sh alongside the OCaml side.
bench_adversarial: $(KT_C_SRC) $(BENCHDIR)/bench_adversarial.c $(KT_HDR)
	$(CC) $(CFLAGS) -o $@ $(KT_C_SRC) $(BENCHDIR)/bench_adversarial.c $(LDFLAGS)

# wc_test must enable KT_PROFILE so the alloc counters are live.
wc_test: $(KT_C_SRC) $(TESTDIR)/wc_test.c $(KT_HDR)
	$(CC) $(CFLAGS) -DKT_PROFILE -o $@ $(KT_C_SRC) $(TESTDIR)/wc_test.c $(LDFLAGS)

# fuzz: 1000 seeds × random workload lengths under ASan + UBSan.
fuzz: $(KT_C_SRC) $(TESTDIR)/fuzz.c $(KT_HDR)
	$(CC) $(CFLAGS_SAN) $(SAN_ASAN) -o $@ $(KT_C_SRC) $(TESTDIR)/fuzz.c $(LDFLAGS)

# diff_workload: deterministic workload trace, paired with
# ocaml/extracted/diff_workload.ml for cross-impl differential testing.
diff_workload: $(KT_C_SRC) $(TESTDIR)/diff_workload.c $(KT_HDR)
	$(CC) $(CFLAGS) -o $@ $(KT_C_SRC) $(TESTDIR)/diff_workload.c $(LDFLAGS)

# cadeque_test: the §6 catenable port self-check (mixed push/inject/pop/
# eject + randomized concat-fold + full drain vs a deque oracle).
cadeque_test: $(KT_ALL_SRC) $(KT_ALL_HDR)
	$(CC) $(CFLAGS_DEBUG) -DKC_PHASE3_SMOKE -o $@ $(KT_ALL_SRC) $(LDFLAGS)

# diff_cadeque: deterministic catenable workload trace, paired with
# ocaml/bench/diff_cadeque.ml against the verified KTFlatCadeque.
diff_cadeque: $(KT_ALL_SRC) $(TESTDIR)/diff_cadeque.c $(KT_ALL_HDR)
	$(CC) $(CFLAGS) -o $@ $(KT_ALL_SRC) $(TESTDIR)/diff_cadeque.c $(LDFLAGS)

# cadeque_asan: catenable port under ASan + UBSan for the fuzz/diff runs.
cadeque_asan: $(KT_ALL_SRC) $(TESTDIR)/diff_cadeque.c $(KT_ALL_HDR)
	$(CC) $(CFLAGS_SAN) $(SAN_ASAN) -o $@ $(KT_ALL_SRC) $(TESTDIR)/diff_cadeque.c $(LDFLAGS)

# fuzz_cadeque: §6 catenable bug hunter (register bank + concat + compaction
# vs a reference model), deterministic seed-sweep under ASan + UBSan.
fuzz_cadeque: $(KT_ALL_SRC) $(TESTDIR)/fuzz_cadeque.c $(KT_ALL_HDR)
	$(CC) $(CFLAGS_SAN) $(SAN_ASAN) -o $@ $(KT_ALL_SRC) $(TESTDIR)/fuzz_cadeque.c $(LDFLAGS)

# fuzz_cadeque_afl: coverage-guided AFL harness (forkserver = fresh state
# per input).  Requires afl-cc on PATH; not built by `all`/`check-all`.
AFL_CC ?= afl-cc
fuzz_cadeque_afl: $(KT_ALL_SRC) $(TESTDIR)/fuzz_cadeque.c $(KT_ALL_HDR)
	AFL_USE_ASAN=1 $(AFL_CC) -O2 -DAFL_HARNESS -DNDEBUG $(CFLAGS_COMMON) \
	    -o $@ $(KT_ALL_SRC) $(TESTDIR)/fuzz_cadeque.c $(LDFLAGS)

# fuzz_cadeque_lf: in-process libFuzzer harness.  Requires clang; not in
# `all`/`check-all`.
FUZZ_CLANG ?= clang
fuzz_cadeque_lf: $(KT_ALL_SRC) $(TESTDIR)/fuzz_cadeque.c $(KT_ALL_HDR)
	$(FUZZ_CLANG) -O1 -g -fsanitize=fuzzer,address,undefined -DFUZZ_LIBFUZZER \
	    -DNDEBUG $(CFLAGS_COMMON) -o $@ $(KT_ALL_SRC) $(TESTDIR)/fuzz_cadeque.c $(LDFLAGS)

# test_threads: 4 threads × independent deques in TLS arenas.
test_threads: $(KT_C_SRC) $(TESTDIR)/test_threads.c $(KT_HDR)
	$(CC) $(CFLAGS_DEBUG) -pthread -o $@ $(KT_C_SRC) $(TESTDIR)/test_threads.c $(LDFLAGS)

# test_persistence_stress: dense COW-sharing under ASan + UBSan.
test_persistence_stress: $(KT_C_SRC) $(TESTDIR)/test_persistence_stress.c $(KT_HDR)
	$(CC) $(CFLAGS_SAN) $(SAN_ASAN) -o $@ $(KT_C_SRC) $(TESTDIR)/test_persistence_stress.c $(LDFLAGS)

# Sanitizer-instrumented test variants (used by check-asan / check-tsan).
test_asan: $(KT_C_SRC) $(TESTDIR)/test.c $(KT_HDR)
	$(CC) $(CFLAGS_SAN) $(SAN_ASAN) -o $@ $(KT_C_SRC) $(TESTDIR)/test.c $(LDFLAGS)

test_threads_tsan: $(KT_C_SRC) $(TESTDIR)/test_threads.c $(KT_HDR)
	$(CC) $(CFLAGS_SAN) $(SAN_TSAN) -pthread -o $@ $(KT_C_SRC) $(TESTDIR)/test_threads.c $(LDFLAGS)

# ---------------------------------------------------------------------
# Run targets
# ---------------------------------------------------------------------

run-test: test
	./test

run-test-debug: test_debug
	./test_debug

run-bench: bench
	./bench

run-wc: wc_test
	./wc_test

run-fuzz: fuzz
	ASAN_OPTIONS=detect_leaks=0 ./fuzz 1000

run-cadeque: cadeque_test
	./cadeque_test 200000

# §6 catenable fuzzer (deterministic seed-sweep under ASan + UBSan).
run-fuzz-cadeque: fuzz_cadeque
	ASAN_OPTIONS=detect_leaks=0 ./fuzz_cadeque 2000

# Coverage-guided AFL campaign (runs until interrupted).  Manual.
run-fuzz-cadeque-afl: fuzz_cadeque_afl
	AFL_SKIP_CPUFREQ=1 AFL_I_DONT_CARE_ABOUT_MISSING_CRASHES=1 \
	  ASAN_OPTIONS=abort_on_error=1:symbolize=0:detect_leaks=0 \
	  afl-fuzz -i $(TESTDIR)/afl_seeds_cadeque -o $(TESTDIR)/afl_findings_cadeque \
	  -- ./fuzz_cadeque_afl

# catenable differential: C vs the verified OCaml extraction.  Generates
# the same deterministic workload on both sides and diffs the sequences.
# Requires the OCaml exe built first:
#   dune build --profile release ocaml/bench/diff_cadeque.exe
OCAML_DIFF_CAD ?= ../_build/default/ocaml/bench/diff_cadeque.exe
run-diff-cadeque: diff_cadeque
	@for seed in 1 2 deadbeef cafef00d 99; do \
	  for N in 20000 200000; do \
	    ./diff_cadeque $$N $$seed > /tmp/kc_c.$$$$ ; \
	    $(OCAML_DIFF_CAD) $$N $$seed > /tmp/kc_o.$$$$ ; \
	    if diff -q /tmp/kc_c.$$$$ /tmp/kc_o.$$$$ >/dev/null; then \
	      echo "cadeque diff seed=$$seed N=$$N: MATCH"; \
	    else \
	      echo "cadeque diff seed=$$seed N=$$N: DIVERGE"; \
	      rm -f /tmp/kc_c.$$$$ /tmp/kc_o.$$$$ ; exit 1; \
	    fi; \
	    rm -f /tmp/kc_c.$$$$ /tmp/kc_o.$$$$ ; \
	  done; \
	done

run-threads: test_threads
	./test_threads 100000

# Cross-impl differential test.  Requires OCaml extraction binary.
run-diff: diff_workload
	@N=$${N:-100000}; SEED=$${SEED:-0x123456789abcdef0}; MODE=$${MODE:-mix}; \
	echo "=== Differential C vs OCaml-extracted at n=$$N seed=$$SEED mode=$$MODE ==="; \
	./diff_workload $$N $$SEED $$MODE > /tmp/c_diff_out.txt; \
	../_build/default/ocaml/extracted/diff_workload.exe $$N $$SEED $$MODE > /tmp/ml_diff_out.txt; \
	diff -q /tmp/c_diff_out.txt /tmp/ml_diff_out.txt && echo "PASS: C and OCaml outputs identical"

run-diff-deep: diff_workload
	@$(MAKE) run-diff N=$${N:-400000} MODE=deep

run-diff-multi: diff_workload
	@SEEDS=$${SEEDS:-16}; N=$${N:-50000}; \
	echo "=== Differential sweep: $$SEEDS seeds × {mix,deep} at n=$$N ==="; \
	fail=0; \
	for s in $$(seq 1 $$SEEDS); do \
	    SEED=$$(printf '0x%016x' $$((s * 2654435761))); \
	    for m in mix deep; do \
	        ./diff_workload $$N $$SEED $$m > /tmp/c_diff_out.txt; \
	        ../_build/default/ocaml/extracted/diff_workload.exe $$N $$SEED $$m > /tmp/ml_diff_out.txt; \
	        if ! diff -q /tmp/c_diff_out.txt /tmp/ml_diff_out.txt > /dev/null; then \
	            echo "FAIL seed=$$SEED mode=$$m"; fail=$$((fail+1)); \
	        fi; \
	    done; \
	done; \
	if [ $$fail -eq 0 ]; then \
	    echo "PASS: $$((SEEDS*2)) traces (mix+deep) all identical"; \
	else \
	    echo "FAIL: $$fail traces diverged"; exit 1; \
	fi

# ---------------------------------------------------------------------
# Composite check targets
# ---------------------------------------------------------------------

# check: fast correctness suite (no sanitizers, no fuzz).  Pre-push gate.
check: run-test run-test-debug run-wc run-threads
	@echo
	@echo "=== check passed: test, test_debug, wc_test, threads ==="

check-asan: test_asan
	@echo "=== ASan + UBSan run ==="
	ASAN_OPTIONS=detect_leaks=0 ./test_asan

check-tsan: test_threads_tsan
	@echo "=== TSan run ==="
	./test_threads_tsan 50000

check-fuzz: fuzz
	@echo "=== fuzz: 1000 seeds × random workloads ==="
	ASAN_OPTIONS=detect_leaks=0 ./fuzz 1000

check-fuzz-cadeque: fuzz_cadeque
	@echo "=== fuzz_cadeque: §6 catenable, 2000 seeds × random programs (ASan+UBSan) ==="
	ASAN_OPTIONS=detect_leaks=0 ./fuzz_cadeque 2000

check-diff:
	@$(MAKE) run-diff N=100000

check-diff-deep:
	@$(MAKE) run-diff-deep N=400000

check-diff-multi:
	@$(MAKE) run-diff-multi SEEDS=16 N=50000

check-persistence-stress: test_persistence_stress
	@echo "=== persistence stress (ASan + UBSan, 64 branches × 200 trunk snapshots) ==="
	ASAN_OPTIONS=detect_leaks=0 ./test_persistence_stress 200 100 64

# check-static: GCC analyzer + Clang static analyzer on the production
# source.  Gates: null-deref, OOB, double-free, malloc-leak, possibly-NULL,
# UAF.  See block comment in the previous Makefile for why uninit is not
# gated (well-known FP rate; ASan + fuzz cover it dynamically).
check-static:
	@echo "=== check-static: gcc -fanalyzer ==="
	$(CC) -fanalyzer -O0 -g -std=c11 -Wall -Wextra \
	    -D_POSIX_C_SOURCE=199310L -I$(INCDIR) -UNDEBUG \
	    -Wno-analyzer-use-of-uninitialized-value \
	    -Werror=analyzer-null-dereference \
	    -Werror=analyzer-possible-null-dereference \
	    -Werror=analyzer-out-of-bounds \
	    -Werror=analyzer-double-free \
	    -Werror=analyzer-use-after-free \
	    -Werror=analyzer-malloc-leak \
	    -c $(KT_C_SRC) -o /tmp/kt_static_check.o
	@rm -f /tmp/kt_static_check.o
	@echo "=== check-static: clang --analyze ==="
	clang --analyze -Xanalyzer -analyzer-output=text \
	    -O0 -g -std=c11 -Wall -Wextra \
	    -D_POSIX_C_SOURCE=199310L -I$(INCDIR) -UNDEBUG \
	    -Xanalyzer -analyzer-disable-checker=core.UndefinedBinaryOperatorResult \
	    -Werror \
	    $(KT_C_SRC)
	@echo "=== check-static passed ==="

check-all: check check-static check-asan check-tsan check-fuzz check-fuzz-cadeque check-diff \
           check-diff-deep check-diff-multi check-persistence-stress
	@echo
	@echo "=== check-all passed: every test layer is green ==="

# ---------------------------------------------------------------------
# Install (lib + header + pkg-config descriptor).
# ---------------------------------------------------------------------

# Generate a pkg-config descriptor at install time so paths are correct.
install: lib
	install -d $(DESTDIR)$(PREFIX)/include
	install -d $(DESTDIR)$(PREFIX)/lib
	install -d $(DESTDIR)$(PREFIX)/lib/pkgconfig
	install -m 644 $(KT_HDR)     $(DESTDIR)$(PREFIX)/include/ktdeque.h
	install -m 644 $(KT_CAD_HDR) $(DESTDIR)$(PREFIX)/include/ktcadeque.h
	install -m 644 $(LIBFILE) $(DESTDIR)$(PREFIX)/lib/$(LIBFILE)
	@echo 'prefix=$(PREFIX)'                       >  ktdeque.pc.tmp
	@echo 'exec_prefix=$${prefix}'                 >> ktdeque.pc.tmp
	@echo 'libdir=$${exec_prefix}/lib'             >> ktdeque.pc.tmp
	@echo 'includedir=$${prefix}/include'          >> ktdeque.pc.tmp
	@echo ''                                       >> ktdeque.pc.tmp
	@echo 'Name: ktdeque'                    >> ktdeque.pc.tmp
	@echo 'Description: Kaplan-Tarjan persistent real-time deque (§4) + O(1)-catenable deque (§6), C port' >> ktdeque.pc.tmp
	@echo 'Version: 0.2.0'                         >> ktdeque.pc.tmp
	@echo 'Libs: -L$${libdir} -l$(LIBNAME)'        >> ktdeque.pc.tmp
	@echo 'Cflags: -I$${includedir}'               >> ktdeque.pc.tmp
	install -m 644 ktdeque.pc.tmp $(DESTDIR)$(PREFIX)/lib/pkgconfig/ktdeque.pc
	@rm -f ktdeque.pc.tmp
	@echo "Installed to $(DESTDIR)$(PREFIX) — ktdeque.h, ktcadeque.h, $(LIBFILE), ktdeque.pc"

uninstall:
	rm -f $(DESTDIR)$(PREFIX)/include/ktdeque.h
	rm -f $(DESTDIR)$(PREFIX)/lib/$(LIBFILE)
	rm -f $(DESTDIR)$(PREFIX)/include/ktcadeque.h
	rm -f $(DESTDIR)$(PREFIX)/lib/pkgconfig/ktdeque.pc

clean:
	rm -f *.o $(LIBFILE)
	@for f in test test_debug wc_test fuzz fuzz_afl diff_workload \
	          test_threads test_persistence_stress test_asan \
	          test_threads_tsan bench bench_perf bench_K0 bench_K4096 prof \
	          cadeque_test diff_cadeque cadeque_asan fuzz_cadeque fuzz_cadeque_afl fuzz_cadeque_lf; do \
	    [ -f "$$f" ] && rm -f "$$f" || true; \
	done
