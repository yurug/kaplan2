# Experiments — perf hypothesis tests, profilers, legacy variants

This directory holds artifacts that are **not part of the public
library**: hypothesis tests written during a perf study, profile
drivers, and two legacy deque variants (`ktdeque_d4cell.c`,
`ktdeque_viennot.c`) kept around for differential testing.  Nothing
here is built by `make all`.  Most files reference
`ktdeque_dequeptr.c` at its old top-level path — when you re-run any
of these from this directory, point them at `../src/ktdeque_dequeptr.c`
and `-I../include`.

## Profiling kt_eject (and friends) with perf + hotspot

> **Historical context.**  When this experiments/ directory was first
> populated, the C `eject` was ~4.5× slower than Viennot OCaml on a
> push-N-then-eject-N workload — that gap motivated the perf study
> below.  After the perf-phase optimisations (N, O, P, R) landed, C
> eject is now **1.6× faster** than Viennot OCaml at K=4096 (see
> `../COMPARISON.md`).  The perf-trace recipe in this directory is
> kept as a reference for future regressions.

## On your laptop

### One-time setup

```sh
sudo apt install linux-perf hotspot          # Debian/Ubuntu
# (Or arch: pacman -S perf hotspot.)
sudo sysctl kernel.perf_event_paranoid=1     # allow user-mode perf
# To make it persistent: edit /etc/sysctl.conf or /etc/sysctl.d/local.conf
```

### Generate a trace

```sh
cd c/experiments
./profile_eject.sh 1000000        # writes perf.data
```

The script:
1. Builds `eject_only` with `-O3 -g -fno-omit-frame-pointer`
2. Runs it under `perf record -F 4000 --call-graph=dwarf`

### Visualize

```sh
hotspot perf.data
```

What to look at:
- **Top-Down View** — shows where time is spent. Expect `green_of_red` to
  dominate (~75% based on gprof).
- **Caller/Callee** — pick `green_of_red`, see who calls it and what it calls.
- **Flame Graph** — width = self time. The wide blocks under
  `green_of_red` are `make_small`, `prefix_concat`, `suffix_concat`.
- **Disassembly** — switch to a hot function, examine which instructions
  retire slowly. High-cost loads = cache stalls; high-cost branches =
  mispredicted dispatch.

### Quick text summary without hotspot

```sh
perf report --stdio --sort=overhead,symbol | head -40
perf annotate --stdio --symbol=green_of_red | less
```

## Comparison drivers

- `eject_only.c` — inject N then eject N (profile the eject phase).
- `inject_only.c` — inject N (control: confirms inject is faster than eject).

Build inject_only with the same flags:

```sh
gcc -O3 -g -fno-omit-frame-pointer -funroll-loops -finline-functions \
    -Wall -Wextra -std=c11 -D_POSIX_C_SOURCE=199310L -DNDEBUG \
    -I../include \
    -o inject_only ../src/ktdeque_dequeptr.c inject_only.c
perf record -F 4000 --call-graph=dwarf -o inject.data -- ./inject_only 1000000
hotspot inject.data
```

## Comparing against Viennot OCaml

The OCaml bench is `_build/default/ocaml/bench/compare.exe`. To get useful
flame graphs from OCaml you need frame pointers — by default the OCaml
runtime omits them. Quick check:

```sh
# Standard run (no frame pointers; flame graph will be shallow but
# perf stat counters work fine):
perf stat -e cycles,instructions,branches,branch-misses,\
cache-references,cache-misses,L1-dcache-load-misses,LLC-load-misses \
    -- _build/default/ocaml/bench/compare.exe
```

Compare the same counters from `./eject_only`. The DELTA tells you
whether the gap is memory-bound (high cache miss rate) or
compute-bound (high IPC but more instructions).

For OCaml flame graphs, build with `ocaml-option-fp`:

```sh
opam install ocaml-variants.5.1.0+options ocaml-option-fp
opam exec -- dune clean
opam exec -- dune build
```

Then `perf record --call-graph=fp` works on the OCaml binary.

## Established baseline (gprof)

- `green_of_red` is 76% of CPU
- `kt_eject` self-time is 4-6%
- `make_small`, `prefix_concat`, `suffix_concat` consume the rest under
  `green_of_red`
- Allocation is bumped from a per-thread arena (see `arena_alloc` in
  ktdeque_dequeptr.c) — should NOT be a malloc bottleneck

Hypotheses to test with the perf trace:
1. **Memory-bound**: high L1/LLC miss rate suggests `kt_buf` (40 B) is
   busting cache during the cascade.
2. **Branch-bound**: high branch-miss rate would point at the
   `kt_color` switch in `make_small`'s 9-case dispatch.
3. **Allocation-bound**: arena_alloc shouldn't dominate, but cumulative
   memory pressure (we leak across the bench) could cause TLB thrash.
