#!/usr/bin/env python3
"""bench/plot_cadeque8.py — render Cadeque8 vs Viennot performance plots.

Reads CSV with columns (n, op, impl, ns_per_op) produced by
ocaml/bench/kc8_csv.exe.  Emits three PNGs in bench/plots/:

  cadeque8-scaling.png    ns/op vs N for push/inject/pop/eject/concat,
                          one subplot per op, Cadeque8 vs Viennot.
  cadeque8-adv.png        ns/op for pop-all after a concat chain of
                          depth ∈ {10, 30, 100, 300, 1000, 3000, 10000}.
  cadeque8-summary.png    side-by-side bar chart at the largest N
                          for a single-glance speedup snapshot.

Usage:
    bench/plot_cadeque8.py <csv> <output_dir>
"""
import csv
import sys
import os
from collections import defaultdict

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

COLORS = {
    "Cadeque8":      "#1f77b4",   # blue
    "Cadeque8_fast": "#2ca02c",   # green
    "Viennot":       "#d62728",   # red
}
MARKERS = {
    "Cadeque8":      "o",
    "Cadeque8_fast": "D",
    "Viennot":       "s",
}
IMPLS = ["Cadeque8", "Cadeque8_fast", "Viennot"]


def read_csv(path):
    """data[op][impl] = list of (n, ns_per_op) sorted by n."""
    data = defaultdict(lambda: defaultdict(list))
    with open(path) as f:
        for row in csv.DictReader(f):
            n = int(row["n"])
            ns = float(row["ns_per_op"])
            data[row["op"]][row["impl"]].append((n, ns))
    for op in data:
        for impl in data[op]:
            data[op][impl].sort()
    return data


def plot_scaling(data, out_path):
    """Five subplots, one per op (push/inject/pop/eject/concat),
    each showing ns/op vs N for both implementations.

    Each subplot uses a log-x scale.  A horizontal line is implicit
    (WC O(1) ⇒ flat); a rising line would be amortized-O(log n) or worse.
    """
    ops = ["push", "inject", "pop", "eject", "concat"]
    fig, axes = plt.subplots(2, 3, figsize=(14, 8))
    fig.suptitle(
        "Cadeque8 vs Viennot — scaling per operation (lower is faster)",
        fontsize=14, fontweight="bold")

    for ax, op in zip(axes.flat, ops):
        ax.set_title(op, fontsize=12)
        for impl in IMPLS:
            pts = data.get(op, {}).get(impl, [])
            if not pts:
                continue
            ns = [p[0] for p in pts]
            ys = [p[1] for p in pts]
            ax.plot(ns, ys,
                    color=COLORS[impl],
                    marker=MARKERS[impl],
                    markersize=6,
                    linewidth=1.6,
                    label=impl)
        ax.set_xscale("log")
        ax.set_xlabel("N (deque size)", fontsize=9)
        ax.set_ylabel("ns / op", fontsize=9)
        ax.grid(True, alpha=0.3)
        ax.legend(fontsize=9)

    # Hide the unused subplot (we have 5 ops, 6 grid cells).
    axes.flat[5].axis("off")

    fig.tight_layout(rect=[0, 0, 1, 0.96])
    fig.savefig(out_path, dpi=110)
    plt.close(fig)


def plot_adversarial(data, out_path):
    """Adversarial workload: pop-all after a deep concat chain.

    Here the x-axis is the total element count (depth × 100), and
    ns/op = total_pop_time / total_elements.  A truly WC-O(1)
    implementation should give a flat line; amortized O(log n) or
    worse should rise.
    """
    fig, ax = plt.subplots(figsize=(8, 5))
    ax.set_title(
        "Adversarial: pop-all after `depth` concats × 100 elts\n"
        "(flat = WC O(1); rising = amortized breaks)",
        fontsize=12, fontweight="bold")

    for impl in ["Cadeque8", "Viennot"]:
        pts = data.get("adv_pop", {}).get(impl, [])
        if not pts:
            continue
        ns = [p[0] for p in pts]
        ys = [p[1] for p in pts]
        ax.plot(ns, ys,
                color=COLORS[impl],
                marker=MARKERS[impl],
                markersize=7,
                linewidth=1.8,
                label=impl)

    ax.set_xscale("log")
    ax.set_xlabel("total elements drained (= depth × 100)", fontsize=10)
    ax.set_ylabel("ns / pop", fontsize=10)
    ax.grid(True, alpha=0.3)
    ax.legend(fontsize=10)

    fig.tight_layout()
    fig.savefig(out_path, dpi=110)
    plt.close(fig)


def plot_summary(data, out_path):
    """Side-by-side bars at the largest N for each op."""
    ops = ["push", "inject", "pop", "eject", "concat"]

    # Pick the largest N across all ops/impls
    all_ns = set()
    for op in ops:
        for impl in IMPLS:
            for (n, _) in data.get(op, {}).get(impl, []):
                all_ns.add(n)
    if not all_ns:
        return
    biggest_n = max(all_ns)

    fig, ax = plt.subplots(figsize=(11, 5.5))
    ax.set_title(
        f"Cadeque8 vs Cadeque8_fast vs Viennot at N = {biggest_n:,} — ns/op",
        fontsize=12, fontweight="bold")

    x = list(range(len(ops)))
    width = 0.27

    vals_by_impl = {impl: [] for impl in IMPLS}
    for op in ops:
        for impl in IMPLS:
            pts = dict(data.get(op, {}).get(impl, []))
            vals_by_impl[impl].append(pts.get(biggest_n, 0))

    offsets = {"Cadeque8": -width, "Cadeque8_fast": 0, "Viennot": width}
    labels  = {"Cadeque8":      "Cadeque8 (verified, option-typed)",
               "Cadeque8_fast": "Cadeque8_fast (verified, flat sum)",
               "Viennot":       "Viennot OCaml (hand-written ref)"}
    for impl in IMPLS:
        ax.bar([xi + offsets[impl] for xi in x],
               vals_by_impl[impl], width,
               color=COLORS[impl], label=labels[impl])

    # Annotate fast/orig ratio (improvement) above each op's bars
    for i, op in enumerate(ops):
        orig = vals_by_impl["Cadeque8"][i]
        fast = vals_by_impl["Cadeque8_fast"][i]
        if orig > 0:
            delta = 100 * (fast - orig) / orig
            sign = "" if delta >= 0 else ""
            top = max(orig, fast, vals_by_impl["Viennot"][i])
            ax.text(i, top * 1.04,
                    f"fast {sign}{delta:+.0f}%",
                    ha="center", fontsize=9,
                    color="#2ca02c" if delta < 0 else "#888")

    ax.set_xticks(x)
    ax.set_xticklabels(ops)
    ax.set_ylabel("ns / op", fontsize=10)
    ax.grid(True, axis="y", alpha=0.3)
    ax.legend(fontsize=9)

    fig.tight_layout()
    fig.savefig(out_path, dpi=110)
    plt.close(fig)


def main():
    if len(sys.argv) != 3:
        print(__doc__, file=sys.stderr)
        sys.exit(2)
    csv_path, out_dir = sys.argv[1], sys.argv[2]
    os.makedirs(out_dir, exist_ok=True)

    data = read_csv(csv_path)

    plot_scaling(data, os.path.join(out_dir, "cadeque8-scaling.png"))
    plot_adversarial(data, os.path.join(out_dir, "cadeque8-adv.png"))
    plot_summary(data, os.path.join(out_dir, "cadeque8-summary.png"))

    print(f"wrote 3 plots to {out_dir}/", file=sys.stderr)


if __name__ == "__main__":
    main()
