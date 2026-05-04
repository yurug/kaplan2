# =====================================================================
# Build / install / test for the kaplan2 KT-deque C library.
#
#   Source layout:
#     include/    public header (ktdeque.h)
#     src/        production source (ktdeque_dequeptr.c)
#     tests/      correctness + fuzz drivers
#     bench/      microbenchmarks
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
        run-fuzz run-diff run-diff-deep run-diff-multi run-threads \
        check check-asan check-tsan check-fuzz \
        check-diff check-diff-deep check-diff-multi check-static \
        check-persistence-stress check-all

# Default goal: library + tests + bench.
all: lib test test_debug bench wc_test fuzz diff_workload test_threads test_persistence_stress

# ---------------------------------------------------------------------
# Library archive — linkable, installable.
# ---------------------------------------------------------------------

lib: $(LIBFILE)

$(LIBFILE): ktdeque.o
	$(AR) rcs $@ $^

ktdeque.o: $(KT_C_SRC) $(KT_HDR)
	$(CC) $(CFLAGS) -c -o $@ $(KT_C_SRC)

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

check-all: check check-static check-asan check-tsan check-fuzz check-diff \
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
	install -m 644 $(KT_HDR)  $(DESTDIR)$(PREFIX)/include/ktdeque.h
	install -m 644 $(LIBFILE) $(DESTDIR)$(PREFIX)/lib/$(LIBFILE)
	@echo 'prefix=$(PREFIX)'                       >  ktdeque.pc.tmp
	@echo 'exec_prefix=$${prefix}'                 >> ktdeque.pc.tmp
	@echo 'libdir=$${exec_prefix}/lib'             >> ktdeque.pc.tmp
	@echo 'includedir=$${prefix}/include'          >> ktdeque.pc.tmp
	@echo ''                                       >> ktdeque.pc.tmp
	@echo 'Name: ktdeque'                    >> ktdeque.pc.tmp
	@echo 'Description: Kaplan-Tarjan persistent real-time deque (worst-case O(1))' >> ktdeque.pc.tmp
	@echo 'Version: 0.1.0'                         >> ktdeque.pc.tmp
	@echo 'Libs: -L$${libdir} -l$(LIBNAME)'        >> ktdeque.pc.tmp
	@echo 'Cflags: -I$${includedir}'               >> ktdeque.pc.tmp
	install -m 644 ktdeque.pc.tmp $(DESTDIR)$(PREFIX)/lib/pkgconfig/ktdeque.pc
	@rm -f ktdeque.pc.tmp
	@echo "Installed to $(DESTDIR)$(PREFIX) — header, $(LIBFILE), ktdeque.pc"

uninstall:
	rm -f $(DESTDIR)$(PREFIX)/include/ktdeque.h
	rm -f $(DESTDIR)$(PREFIX)/lib/$(LIBFILE)
	rm -f $(DESTDIR)$(PREFIX)/lib/pkgconfig/ktdeque.pc

clean:
	rm -f *.o $(LIBFILE)
	@for f in test test_debug wc_test fuzz fuzz_afl diff_workload \
	          test_threads test_persistence_stress test_asan \
	          test_threads_tsan bench bench_perf bench_K0 bench_K4096 prof; do \
	    [ -f "$$f" ] && rm -f "$$f" || true; \
	done
