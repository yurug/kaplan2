CC      = gcc
CFLAGS  = -O3 -funroll-loops -finline-functions -fomit-frame-pointer -Wall -Wextra -std=c11 -D_POSIX_C_SOURCE=199309L -DNDEBUG
LDFLAGS =

# Default C source: ktdeque_dequeptr.c (full DequePtr translation
# with make_red push/inject and make_green pop/eject; mirrors the certified
# imperative DSL in rocq/KTDeque/DequePtr/Footprint.v).
# Override with: make KT_C_SRC=ktdeque_viennot.c (older Viennot variant)
# or make KT_C_SRC=ktdeque.c (older D4Cell, amortized).
KT_C_SRC ?= ktdeque_dequeptr.c

# Sanitizer flags: ASan + UBSan for memory + UB checks; TSan for races.
# Used by check-asan and test_threads_tsan targets.
SAN_ASAN  = -fsanitize=address,undefined -fno-omit-frame-pointer
SAN_TSAN  = -fsanitize=thread -fno-omit-frame-pointer

CFLAGS_DEBUG = -O2 -Wall -Wextra -std=c11 -D_POSIX_C_SOURCE=199309L -UNDEBUG -g
CFLAGS_SAN   = -O1 -Wall -Wextra -std=c11 -D_POSIX_C_SOURCE=199309L -DNDEBUG -g

.PHONY: all clean \
        run-test run-test-debug run-bench run-wc \
        run-fuzz run-diff run-threads \
        check check-asan check-tsan check-fuzz check-diff check-all

all: test test_debug bench wc_test fuzz diff_workload test_threads

# ----- Main targets -----

test: ktdeque.o test.o
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)

# test_debug: -UNDEBUG so green_of_red regularity asserts execute.
test_debug: $(KT_C_SRC) test.c ktdeque.h
	$(CC) $(CFLAGS_DEBUG) -o $@ $(KT_C_SRC) test.c $(LDFLAGS)

bench: ktdeque.o bench.o
	$(CC) $(CFLAGS) -o $@ $^ $(LDFLAGS)

# wc_test must enable KT_PROFILE so the alloc counters are live.
wc_test: wc_test.c $(KT_C_SRC) ktdeque.h
	$(CC) $(CFLAGS) -DKT_PROFILE -o $@ $(KT_C_SRC) wc_test.c $(LDFLAGS)

# fuzz: 1000 seeds × random workload lengths.  Build with sanitizers by
# default since fuzzing's value comes from catching memory/UB bugs.
fuzz: fuzz.c $(KT_C_SRC) ktdeque.h
	$(CC) $(CFLAGS_SAN) $(SAN_ASAN) -o $@ $(KT_C_SRC) fuzz.c $(LDFLAGS)

# diff_workload: deterministic workload trace, paired with
# ocaml/extracted/diff_workload.ml for cross-impl differential testing.
diff_workload: diff_workload.c $(KT_C_SRC) ktdeque.h
	$(CC) $(CFLAGS) -o $@ $(KT_C_SRC) diff_workload.c $(LDFLAGS)

# test_threads: 4 threads × independent deques in TLS arenas.
test_threads: test_threads.c $(KT_C_SRC) ktdeque.h
	$(CC) $(CFLAGS_DEBUG) -pthread -o $@ $(KT_C_SRC) test_threads.c $(LDFLAGS)

ktdeque.o: $(KT_C_SRC) ktdeque.h
	$(CC) $(CFLAGS) -c -o $@ $(KT_C_SRC)

%.o: %.c ktdeque.h
	$(CC) $(CFLAGS) -c -o $@ $<

# ----- Sanitizer-instrumented test variants -----

# test under ASan + UBSan; catches memory bugs.  Disable leak detection
# at run time (ASAN_OPTIONS=detect_leaks=0) — see check-asan target.
test_asan: test.c $(KT_C_SRC) ktdeque.h
	$(CC) $(CFLAGS_SAN) $(SAN_ASAN) -o $@ $(KT_C_SRC) test.c $(LDFLAGS)

# test under TSan; catches data races.
test_threads_tsan: test_threads.c $(KT_C_SRC) ktdeque.h
	$(CC) $(CFLAGS_SAN) $(SAN_TSAN) -pthread -o $@ $(KT_C_SRC) test_threads.c $(LDFLAGS)

# ----- Run targets (single binary) -----

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

# Cross-impl differential test.  Requires the OCaml extraction to be
# built first (run from repo root: `dune build ocaml/extracted/diff_workload.exe`).
run-diff: diff_workload
	@N=$${N:-100000}; \
	echo "=== Differential C vs OCaml-extracted at n=$$N ==="; \
	./diff_workload $$N > /tmp/c_diff_out.txt; \
	../_build/default/ocaml/extracted/diff_workload.exe $$N > /tmp/ml_diff_out.txt; \
	diff -q /tmp/c_diff_out.txt /tmp/ml_diff_out.txt && echo "PASS: C and OCaml outputs identical"

# ----- Composite check targets -----

# check: fast set of correctness tests (no sanitizers, no fuzz).
# Suitable for every commit / pre-push hook.
check: run-test run-test-debug run-wc run-threads
	@echo
	@echo "=== check passed: test, test_debug, wc_test, threads ==="

# check-asan: run main test suite under ASan + UBSan.
check-asan: test_asan
	@echo "=== ASan + UBSan run ==="
	ASAN_OPTIONS=detect_leaks=0 ./test_asan

# check-tsan: run thread test under TSan.
check-tsan: test_threads_tsan
	@echo "=== TSan run ==="
	./test_threads_tsan 50000

# check-fuzz: 1000-seed fuzz under ASan + UBSan.
check-fuzz: fuzz
	@echo "=== fuzz: 1000 seeds × random workloads ==="
	ASAN_OPTIONS=detect_leaks=0 ./fuzz 1000

# check-diff: cross-impl differential at n=100k.
check-diff:
	@$(MAKE) run-diff N=100000

# check-all: full test matrix.  Suitable for nightly CI.
check-all: check check-asan check-tsan check-fuzz check-diff
	@echo
	@echo "=== check-all passed: every test layer is green ==="

clean:
	rm -f *.o test test_debug bench wc_test \
	      fuzz diff_workload test_threads \
	      test_asan test_threads_tsan \
	      bench_arena_* bench_K* bench_perf prof
