#!/usr/bin/env python3
"""bench/adversarial_plot.py — render persistent-fork bench plot.

Reads a CSV with columns (impl, depth, size, ns_per_op) emitted by
adversarial.exe and renders one PNG with one line per impl: ns/op vs
cascade depth (= log_2(N)).

KT and Viennot should be flat (worst-case O(1)).  D4_primed and
D4_sequential should grow linearly with depth (worst-case O(log N)).

Usage:
    bench/adversarial_plot.py <csv> <plot_path> <md_summary>
"""
import csv
import sys
from collections import defaultdict
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


COLORS = {
    "KT":             "#2ca02c",
    "Viennot":        "#d62728",
    "D4_primed":      "#9467bd",
    "D4_sequential":  "#8c564b",
}
MARKERS = {"KT": "s", "Viennot": "^", "D4_primed": "D", "D4_sequential": "x"}
IMPL_ORDER = ("KT", "Viennot", "D4_primed", "D4_sequential")


def read_csv(path):
    """Return data[impl] = list of (depth, size, ns), sorted by depth."""
    data = defaultdict(list)
    with open(path) as f:
        for row in csv.DictReader(f):
            depth = int(row["depth"])
            size = int(row["size"])
            ns = float(row["ns_per_op"])
            data[row["impl"]].append((depth, size, ns))
    for impl in data:
        data[impl].sort()
    return data


def render(data, out_path):
    fig, ax = plt.subplots(figsize=(8.0, 5.0))
    for impl in IMPL_ORDER:
        if impl not in data:
            continue
        rows = data[impl]
        xs = [r[0] for r in rows]
        ys = [r[2] for r in rows]
        ax.plot(
            xs, ys,
            label=impl,
            color=COLORS[impl],
            marker=MARKERS[impl],
            linewidth=1.5,
            markersize=5,
        )
    ax.set_xlabel("Cascade depth d  (logical size = 5·(2^(d+1)-1))")
    ax.set_ylabel("ns / op (lower is better)")
    ax.set_title(
        "Persistent-fork: M push ops from a saved state\n"
        "WC O(1) (KT, Viennot) flat; amortized O(log N) (D4) grows linearly with depth"
    )
    ax.grid(True, which="both", alpha=0.3)
    ax.set_ylim(bottom=0)
    ax.legend(loc="upper left")
    fig.tight_layout()
    fig.savefig(out_path, dpi=120)
    plt.close(fig)


def write_md(data, md_path, csv_path):
    impls = [i for i in IMPL_ORDER if i in data]
    depths = sorted({d for impl in impls for d, _, _ in data[impl]})

    lines = []
    lines.append("# Adversarial persistent-fork bench\n")
    lines.append(f"Source CSV: `{csv_path}`.\n")
    lines.append(
        "Per-op cost when the *same* saved state is the LHS of M=200k push "
        "ops.  Persistence breaks D4's amortized analysis: every op pays "
        "the worst-case cost of the saved state (O(log N)), no credits "
        "carry across ops.  KT and Viennot's WC O(1) makes the cost "
        "state-independent — so their lines are flat.\n"
    )
    header = "| Depth |  Size  |" + "".join(f" {i} |" for i in impls)
    sep = "| ---: | ---: |" + " ---: |" * len(impls)
    lines.append(header)
    lines.append(sep)
    for d in depths:
        size = next((s for impl in impls
                     for dd, s, _ in data[impl] if dd == d), 0)
        row = [f"{d}", f"{size:,d}"]
        for impl in impls:
            ns_list = [v for dd, _, v in data[impl] if dd == d]
            row.append(f"{ns_list[0]:6.1f}" if ns_list else "—")
        lines.append("| " + " | ".join(row) + " |")
    lines.append("")
    lines.append("All values are ns/op (lower is better).")
    with open(md_path, "w") as f:
        f.write("\n".join(lines))


def main():
    if len(sys.argv) != 4:
        print("usage: adversarial_plot.py <csv> <png> <md>", file=sys.stderr)
        sys.exit(2)
    csv_path, png_path, md_path = sys.argv[1:]
    data = read_csv(csv_path)
    render(data, png_path)
    write_md(data, md_path, csv_path)


if __name__ == "__main__":
    main()
