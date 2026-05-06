#!/usr/bin/env python3
"""bench/plot.py — render scaling plots from sweep CSV.

Reads a CSV with columns (n, op, impl, ns_per_op) produced by
bench/sweep.sh, emits one PNG per op (push, pop, inject, eject, mixed)
showing ns/op vs n on a log-x axis with one line per implementation
(C, KTDeque, Viennot).  Also writes a Markdown summary table.

Usage:
    bench/plot.py <csv> <plot_dir> <md_summary_file>
"""
import csv
import sys
from collections import defaultdict
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


def read_csv(path):
    """Return data[op][impl] = list of (n, ns_per_op), sorted by n."""
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


COLORS = {"C": "#1f77b4", "KTDeque": "#2ca02c", "Viennot": "#d62728"}
MARKERS = {"C": "o", "KTDeque": "s", "Viennot": "^"}


def render_op(op, impl_data, out_path):
    """impl_data: { impl_name -> [(n, ns), ...] }"""
    fig, ax = plt.subplots(figsize=(7.5, 4.5))
    for impl in ("C", "KTDeque", "Viennot"):
        if impl not in impl_data:
            continue
        ns = impl_data[impl]
        xs = [p[0] for p in ns]
        ys = [p[1] for p in ns]
        ax.plot(
            xs,
            ys,
            label=impl,
            color=COLORS[impl],
            marker=MARKERS[impl],
            linewidth=1.5,
            markersize=5,
        )
    ax.set_xscale("log")
    ax.set_xlabel("N (operations)")
    ax.set_ylabel("ns / op (lower is better)")
    title_extra = " — total ops/iter = 3" if op == "mixed" else ""
    ax.set_title(f"Scaling: {op}{title_extra}")
    ax.grid(True, which="both", alpha=0.3)
    ax.set_ylim(bottom=0)
    ax.legend()
    fig.tight_layout()
    fig.savefig(out_path, dpi=120)
    plt.close(fig)


def write_md_summary(data, md_path, csv_path):
    sizes = sorted(
        {n for op in data for impl in data[op] for n, _ in data[op][impl]}
    )
    impls = ["C", "KTDeque", "Viennot"]
    ops = ["push", "inject", "pop", "eject", "mixed"]
    lines = []
    lines.append("# Three-way scaling sweep\n")
    lines.append(f"Source CSV: `{csv_path}`.\n")
    lines.append(
        "ns/op for each (op, impl) at each N.  Lower is better.  "
        "Flat columns are the WC O(1) signal: per-op cost does not "
        "grow with N.\n"
    )
    for op in ops:
        if op not in data:
            continue
        lines.append(f"## {op}\n")
        header = (
            "| N |"
            + "".join(f" {impl} (ns/op) |" for impl in impls)
        )
        sep = "| ---: |" + " ---: |" * len(impls)
        lines.append(header)
        lines.append(sep)
        for n in sizes:
            row = [f"{n:>12,d}"]
            for impl in impls:
                ns_list = [v for nn, v in data[op].get(impl, []) if nn == n]
                if ns_list:
                    row.append(f"{ns_list[0]:8.1f}")
                else:
                    row.append("—")
            lines.append("| " + " | ".join(row) + " |")
        lines.append("")
    with open(md_path, "w") as f:
        f.write("\n".join(lines))


def main():
    if len(sys.argv) != 4:
        print("usage: plot.py <csv> <plot_dir> <md_summary>", file=sys.stderr)
        sys.exit(2)
    csv_path, plot_dir, md_path = sys.argv[1:]
    data = read_csv(csv_path)
    for op in ("push", "inject", "pop", "eject", "mixed"):
        if op in data:
            out = f"{plot_dir}/scaling-{op}.png"
            render_op(op, data[op], out)
            print(f"  wrote {out}")
    write_md_summary(data, md_path, csv_path)


if __name__ == "__main__":
    main()
