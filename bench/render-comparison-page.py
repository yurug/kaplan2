#!/usr/bin/env python3
"""render-comparison-page.py — build the self-contained comparison web page
kb/viennot-comparison.html from a dated cadeque benchmark result.

Usage:
    bench/render-comparison-page.py [bench/results/cadeque-compare-YYYY-MM-DD.md]

Reads the markdown table emitted by bench/cadeque-compare.sh and renders:
  - log-log SVG small-multiple charts (one per workload, KT vs Vi),
  - the full results table,
  - the qualitative comparison prose (kept in sync with
    kb/reports/viennot-comparison-2026-06-11.md).

No external dependencies; output is a single static HTML file.
"""

import math
import re
import sys
import glob
import html
import os

# ---------------------------------------------------------------- input

if len(sys.argv) > 1:
    src = sys.argv[1]
else:
    cands = sorted(glob.glob("bench/results/cadeque-compare-*.md"))
    if not cands:
        sys.exit("no bench/results/cadeque-compare-*.md found; run `make bench-cadeque` first")
    src = cands[-1]

text = open(src).read()

meta = {}
for key in ("date", "kernel", "ocaml"):
    m = re.search(rf"^- {key}: (.+)$", text, re.M)
    meta[key] = m.group(1).strip() if m else "?"

sizes = []
rows = {}            # workload -> {impl -> [cell str]}
order = []
for line in text.splitlines():
    if line.startswith("| workload |"):
        sizes = [c.strip()[2:] for c in line.split("|")[3:-1]]
        continue
    m = re.match(r"\| (.+?) \| (KT|KTf|Vi) \| (.+) \|$", line)
    if m:
        w, impl, cells = m.group(1).strip(), m.group(2), [c.strip() for c in m.group(3).split("|")]
        if w not in rows:
            rows[w] = {}
            order.append(w)
        rows[w][impl] = cells

if not sizes or not order:
    sys.exit(f"could not parse a results table out of {src}")

NS = [int(s) for s in sizes]

# ---------------------------------------------------------------- charts

KT_COL = "#9db7d4"   # model layer: muted — the honest baseline
KTF_COL = "#0066cc"  # production (verified kt4 buffers)
VI_COL = "#d4731a"

def chart(workload):
    W, H = 330, 235
    x0, x1 = 48, 312
    y0, y1 = 16, 188          # y0 = top, y1 = axis
    lx0, lx1 = math.log10(NS[0]), math.log10(NS[-1])
    ly0, ly1 = 1.0, 6.0       # 10 ns .. 1,000,000 ns

    def px(n):
        return x0 + (math.log10(n) - lx0) / (lx1 - lx0) * (x1 - x0)

    def py(v):
        l = min(max(math.log10(v), ly0), ly1)
        return y1 - (l - ly0) / (ly1 - ly0) * (y1 - y0)

    s = [f'<svg viewBox="0 0 {W} {H}" class="chart" role="img" '
         f'aria-label="ns/op vs n, {html.escape(workload)}">']
    # gridlines + y labels (decades)
    for d in range(1, 7):
        y = py(10 ** d)
        lab = {1: "10", 2: "100", 3: "1k", 4: "10k", 5: "100k", 6: "1M"}[d]
        s.append(f'<line x1="{x0}" y1="{y:.1f}" x2="{x1}" y2="{y:.1f}" class="grid"/>')
        s.append(f'<text x="{x0-5}" y="{y+3.5:.1f}" class="ylab">{lab}</text>')
    # x ticks
    for n in NS:
        x = px(n)
        lab = {1000: "1k", 10000: "10k", 100000: "100k", 1000000: "1M"}.get(n, str(n))
        s.append(f'<line x1="{x:.1f}" y1="{y1}" x2="{x:.1f}" y2="{y1+4}" class="tick"/>')
        s.append(f'<text x="{x:.1f}" y="{y1+15}" class="xlab">{lab}</text>')
    s.append(f'<rect x="{x0}" y="{y0}" width="{x1-x0}" height="{y1-y0}" class="frame"/>')

    capped = False
    for impl, col in (("KT", KT_COL), ("KTf", KTF_COL), ("Vi", VI_COL)):
        pts = []
        for n, cell in zip(NS, rows[workload].get(impl, [])):
            if cell.startswith("("):
                if impl == "KT":
                    capped = True
                break
            pts.append((px(n), py(float(cell))))
        if len(pts) >= 2:
            d = " ".join(f"{x:.1f},{y:.1f}" for x, y in pts)
            s.append(f'<polyline points="{d}" fill="none" stroke="{col}" stroke-width="2"/>')
        for x, y in pts:
            s.append(f'<circle cx="{x:.1f}" cy="{y:.1f}" r="3" fill="{col}"/>')
        if capped and impl == "KT" and pts:
            x, y = pts[-1]
            s.append(f'<text x="{min(x+8, x1-78):.1f}" y="{max(y-8, y0+10):.1f}" '
                     f'class="cap">&#8599; quadratic</text>')
            capped = False
    s.append(f'<text x="{(x0+x1)/2:.0f}" y="{H-3}" class="title">'
             f'{html.escape(workload)}</text>')
    s.append("</svg>")
    return "\n".join(s)

charts = "\n".join(f'<div class="cell">{chart(w)}</div>' for w in order)

# ---------------------------------------------------------------- table

def fmt(cell):
    if cell.startswith("("):
        return f'<td class="cap-cell">{html.escape(cell)}</td>'
    v = float(cell)
    return f"<td>{v:,.0f}</td>"

trs = []
for w in order:
    impls = [i for i in ("KT", "KTf", "Vi") if i in rows[w]]
    first = True
    for impl in impls:
        cls = {"KT": "kt", "KTf": "ktf", "Vi": "vi"}[impl]
        lead = (f'<td rowspan="{len(impls)}" class="wl">{html.escape(w)}</td>'
                if first else "")
        first = False
        trs.append(f'<tr>{lead}<td class="impl {cls}">{impl}</td>'
                   + "".join(fmt(c) for c in rows[w][impl]) + "</tr>")
table = "\n".join(trs)
size_heads = "".join(f"<th>n = {n:,}</th>" for n in NS)

# ---------------------------------------------------------------- page

page = f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Catenable deques: kaplan2 vs Viennot et al. — comparison &amp; benchmark</title>
<style>
  :root {{
    --bg:        #fdfdfa;
    --fg:        #1a1a1a;
    --muted:     #6a6a6a;
    --accent:    #0066cc;
    --accent-bg: #e8f3ff;
    --code-bg:   #f5f3ef;
    --warn-bg:   #fff8e1;
    --warn-bd:   #d4a017;
    --ok-bg:     #e8f5e8;
    --ok-bd:     #2e7d32;
    --bad-bg:    #ffeaea;
    --bad-bd:    #c62828;
    --rule:      #ddd6c8;
    --kt:        {KT_COL};
    --ktf:       {KTF_COL};
    --vi:        {VI_COL};
  }}
  html {{ background: var(--bg); color: var(--fg); }}
  body {{
    max-width: 980px;
    margin: 2em auto;
    padding: 0 1.5em;
    font: 16px/1.6 -apple-system, "Helvetica Neue", Helvetica, Arial, sans-serif;
  }}
  h1, h2, h3 {{ font-weight: 600; line-height: 1.25; }}
  h1 {{ font-size: 1.9em; border-bottom: 2px solid var(--rule); padding-bottom: .3em; }}
  h2 {{ font-size: 1.45em; margin-top: 2em; border-bottom: 1px solid var(--rule); padding-bottom: .2em; }}
  h3 {{ font-size: 1.15em; margin-top: 1.5em; }}
  a {{ color: var(--accent); text-decoration: none; border-bottom: 1px dotted var(--accent); }}
  a:hover {{ border-bottom-style: solid; }}
  code {{ font-family: "SF Mono", Consolas, "Liberation Mono", monospace;
         font-size: .92em; background: var(--code-bg); padding: 1px 4px; border-radius: 3px; }}
  pre {{ background: var(--code-bg); padding: 12px 16px; border-radius: 5px;
        border-left: 3px solid var(--accent); overflow-x: auto; }}
  pre code {{ background: none; padding: 0; }}
  .tldr {{ background: var(--accent-bg); border-left: 4px solid var(--accent);
          padding: 14px 18px; border-radius: 4px; margin: 1.2em 0; }}
  .honest {{ background: var(--warn-bg); border-left: 4px solid var(--warn-bd);
            padding: 14px 18px; border-radius: 4px; margin: 1.2em 0; }}
  .win {{ background: var(--ok-bg); border-left: 4px solid var(--ok-bd);
         padding: 14px 18px; border-radius: 4px; margin: 1.2em 0; }}
  table {{ border-collapse: collapse; margin: 1.2em 0; width: 100%; font-size: .95em; }}
  th, td {{ border: 1px solid var(--rule); padding: 6px 10px; text-align: left; }}
  th {{ background: var(--code-bg); }}
  .results td {{ text-align: right; font-variant-numeric: tabular-nums; }}
  .results td.wl {{ text-align: left; }}
  .results td.impl {{ text-align: center; font-weight: 600; }}
  .results .kt {{ color: var(--kt); }}
  .results .ktf {{ color: var(--ktf); font-weight: 700; }}
  .results .vi {{ color: var(--vi); }}
  .results .cap-cell {{ color: var(--bad-bd); background: var(--bad-bg); text-align: center; }}
  .grid-charts {{ display: grid; grid-template-columns: repeat(auto-fill, minmax(300px, 1fr));
                 gap: 14px; margin: 1.2em 0; }}
  .cell {{ background: #fff; border: 1px solid var(--rule); border-radius: 6px; padding: 6px; }}
  .chart {{ width: 100%; height: auto; display: block; }}
  .chart .grid  {{ stroke: #eee8dc; stroke-width: 1; }}
  .chart .frame {{ fill: none; stroke: var(--rule); stroke-width: 1; }}
  .chart .tick  {{ stroke: var(--muted); stroke-width: 1; }}
  .chart .ylab  {{ font: 9px sans-serif; fill: var(--muted); text-anchor: end; }}
  .chart .xlab  {{ font: 9px sans-serif; fill: var(--muted); text-anchor: middle; }}
  .chart .title {{ font: 11px sans-serif; fill: var(--fg); text-anchor: middle; font-weight: 600; }}
  .chart .cap   {{ font: 10px sans-serif; fill: var(--bad-bd); }}
  .legend {{ margin: .4em 0 0; color: var(--muted); font-size: .92em; }}
  .legend .sw {{ display: inline-block; width: 22px; height: 3px; vertical-align: middle;
                margin: 0 6px 0 14px; }}
  .meta {{ color: var(--muted); font-size: .9em; }}
  footer {{ margin-top: 3em; padding-top: 1em; border-top: 1px solid var(--rule);
           color: var(--muted); font-size: .9em; }}
</style>
</head>
<body>

<h1>Catenable deques: <span style="color:var(--kt)">kaplan2</span> vs
<span style="color:var(--vi)">Viennot&nbsp;et&nbsp;al.</span></h1>
<p class="meta">Qualitative comparison and head-to-head benchmark of two mechanized
Kaplan–Tarjan (JACM 1999, §6) catenable deques · {html.escape(meta["date"])}</p>

<div class="tldr">
<strong>TL;DR.</strong> Two complete mechanizations of KT99 §6 exist side by side:
our extrinsic rebuild (<code>rocq/KTDeque/Catenable/</code>, keystone closed 2026-06-11)
and Viennot/Wendling/Guéneau/Pottier's intrinsic development.
<em>Functional verification: parity. Mechanized worst-case cost bound: ours only.
Production wall-clock: our verified artifact (<strong>KTf</strong> — the OpsFast
mirror plus the verified fusion pass of OpsFused.v, over verified §4-deque buffers)
is <strong>faster than Viennot's hand-written cadeque on 7 of the 9 workloads</strong>
(both drains, mixed, all three concat patterns, persistent forks — up to 2.4× on
the concat+pop interleave); their build-side push/inject remain ~1.3× ahead, a gap
that lives inside the §4 buffer's push path.</em>
</div>

<h2>1 · The two contenders</h2>
<table>
<tr><th></th><th style="color:var(--kt)">Ours — kaplan2 rebuild</th>
<th style="color:var(--vi)">Viennot et al. (VWGP)</th></tr>
<tr><td>Source</td>
<td><code>rocq/KTDeque/Catenable/</code> — 11 files, 10,631 LOC</td>
<td><code>theory/Cadeque/</code> — 6 files, ~2,040 LOC (+ shared <code>theory/Deque/</code>)</td></tr>
<tr><td>Prover &amp; tooling</td>
<td>Rocq 9.1.1, vanilla Ltac, <strong>zero plugins</strong> (ADR-0004)</td>
<td>Coq 8.19 + Equations + coq-hammer (<code>hauto</code>) + aac-tactics</td></tr>
<tr><td>Encoding</td>
<td><strong>Extrinsic</strong>: plain nested inductives; sizes/colours/levels/regularity
live in one Prop invariant <code>J&nbsp;=&nbsp;chain_wf&nbsp;∧&nbsp;chain_ends_green&nbsp;∧&nbsp;chain_leveled&nbsp;0</code></td>
<td><strong>Intrinsic</strong>: GADTs indexed by level/arity/kind/colour;
<code>node_coloring</code>, <code>triple_coloring</code>, <code>regularity</code> are inductive <em>type</em> families</td></tr>
<tr><td>Headline statement</td>
<td>Six keystone theorems (<code>CatKeystone.v</code>): every op total on regular inputs,
preserves <code>J</code>, exact sequence semantics — incl. concat of two <em>arbitrary</em>
regular deques; <code>Print Assumptions</code> closed</td>
<td><code>Summary.v</code>: ops inhabit both the intrinsic and extrinsic
<code>CADEQUE</code> signatures with sequence correctness;
<code>Print Assumptions everything</code> closed</td></tr>
<tr><td>Cost claim</td>
<td><strong>Mechanized</strong>: <code>Cost.v:cat_wc_o1</code> — buffer primitives per op
≤ a closed constant (push/inject ≤ 4, concat ≤ 43, pop/eject ≤ 145)</td>
<td>Not mechanized — WC O(1) argued in the paper; the types enforce the structure
the argument needs, but no cost theorem exists in the development</td></tr>
<tr><td>Buffers</td>
<td>Model layer: buffers = <code>list</code>.  Production
(<code>OpsFast.v</code>, proved equal to the frozen ops): buffers remapped at
extraction to <code>Fastbuf</code> = our verified §4 deque + O(1) size</td>
<td>Production: buffers = their §4 deque throughout, in theory and in
<code>lib/</code></td></tr>
<tr><td>OCaml artifact</td>
<td><code>kTCadequeFast.ml</code> (production, keystone-transferred via
<code>FastKeystone.v</code>) + <code>kTCadeque.ml</code> (model baseline)</td>
<td>Hand-written production <code>lib/cadeque*.ml</code> <em>and</em> a tuned extraction</td></tr>
</table>

<h2>2 · Qualitative comparison — five differences that matter</h2>

<h3>2.1 Where the invariant lives</h3>
<p>Their GADT indices make ill-coloured structures unrepresentable: a mis-bundled packet
simply does not typecheck, so a whole class of bugs is impossible <em>before any proof is
written</em>. The price is rigidity — the mutually-indexed type families freeze the
design, and refining an invariant means re-indexing every constructor and function.
Our <code>J</code> is one Prop that was refined <strong>in place twice during
discharge</strong> (the top-green clause, then the level-stratification clause) without
touching a single operation. The rebuild methodology — freeze the ops first, grow the
invariant under proof pressure — is only possible extrinsically.</p>

<h3>2.2 What failing proofs buy</h3>
<p>Because our ops are untyped until <code>J</code> speaks, three genuine operation bugs
(concat's childless small-side lift, the pair-collapse re-crowning in pop/eject, and
repair's double-degradation) survived until the corresponding lemmas refused to close —
the proofs acted as the type checker. In their development the same bugs are caught
earlier, by the indices. Net: intrinsic catches structure bugs at definition time;
extrinsic catches them at proof time but tolerates a moving design.</p>

<h3>2.3 Proof-text economy</h3>
<p>Their cadeque theory is ~5× smaller than ours. Equations, dependent pattern matching
and <code>hauto</code> discharge the bookkeeping that we do by hand in ~7,000 lines of
structured Ltac. In exchange we depend on nothing but the kernel and stdlib — no plugin
version pinning, and every proof is a readable forward script (the maintainability bet
recorded in ADR-0004).</p>

<h3>2.4 The cost claim — our main content differentiator</h3>
<p>The Kaplan–Tarjan hard rule (<em>worst-case</em>, not amortized) is a
<strong>theorem</strong> here: <code>cat_wc_o1</code> counts buffer primitives along
every branch of the frozen ops. VWGP's complexity claim lives in their paper's prose;
their mechanization scope is functional correctness.  And the
buffer-primitives-to-wall-clock link is now real on our side too: the production
artifact (<strong>KTf</strong>) implements every counted primitive with the verified
§4 deque, so the mechanized constants translate directly into the flat lines in the
charts below.</p>

<h3>2.5 The port that proves itself — and optimizes inside the prover</h3>
<p>The production artifact is not a hand-written port: <code>OpsFast.v</code> mirrors
every frozen operation against ~15 named buffer primitives, and each mirror carries an
<code>op_f&nbsp;=&nbsp;op</code> equality lemma — the machine-checked diff of the
port.  On top of it, <code>OpsFused.v</code> applies classic compiler transformations
<em>as verified Rocq program transformations</em>: case-of-case fusion of the packet
update (the intermediate (node,&nbsp;child) pair vanishes; the Y/O absorb arms
deforest the rebuilt child cell), and deforestation of
<code>repair&nbsp;∘&nbsp;tree_of</code> on the removal paths (the root colour is
computed once; the duplicate packet teardown and re-allocation disappear; childless
rebuilds skip repair outright).  Each fused function carries an equality proof down
to the frozen ops, so the keystone bundle transfers verbatim
(<code>FastKeystone.v</code>, six theorems, <code>Print Assumptions</code> closed).
The fusion pass alone bought 20–30% on every removal-side workload.
The only trusted seam is 17 one-line <code>Extract Constant</code> directives mapping
the primitives to <code>Fastbuf</code> (= <code>kt4</code> + a size field), each
implementing a one-line list definition with an already-verified deque operation.</p>

<h3>2.6 Statement-strength parity</h3>
<p>Both developments state concat on two <em>arbitrary</em> regular deques (the clause
our archived Cadeque9 could not even state), both close pop/eject with repair, and both
have a clean axiom audit. At the level of "what is mechanically known about KT99 §6
functional behaviour", the two developments are equivalent.</p>

<h2>3 · Benchmark</h2>
<p>Harness: <code>ocaml/bench/cadeque_compare.ml</code> via
<code>make bench-cadeque</code>. Both implementations run the same nine workloads in one
process, swept over n ∈ {{1k, 10k, 100k, 1M}}; a sequence-semantics self-check (both
must agree on the represented list) passes before any timing; a projected-time guard
prints <em>(&gt;cap)</em> instead of letting a quadratic cell run for minutes.</p>
<p class="meta">Environment: {html.escape(meta["kernel"])} · OCaml {html.escape(meta["ocaml"])} ·
single thread, single process, no statistical post-processing.</p>

<div class="honest">
<strong>Three implementations, one table.</strong>
<strong>KT</strong> is the model-layer extraction (list buffers — quadratic
inject/eject by contract; kept as the honest baseline).
<strong>KTf</strong> is the production extraction: the verified OpsFast mirror with
buffers remapped to the proven §4 deque + O(1) size — worst-case O(1) wall-clock on
every operation.
<strong>Vi</strong> is Viennot's hand-written cadeque.
</div>

<h3>3.1 Scaling charts</h3>
<p class="legend">ns per operation (log) vs n (log) — lower is better.
<span class="sw" style="background:var(--kt)"></span> KT (ours, model layer — baseline)
<span class="sw" style="background:var(--ktf)"></span> KTf (ours, production: verified kt4 buffers)
<span class="sw" style="background:var(--vi)"></span> Vi (Viennot, hand-written)</p>

<div class="grid-charts">
{charts}
</div>

<h3>3.2 Full results</h3>
<table class="results">
<tr><th>workload</th><th>impl</th>{size_heads}</tr>
{table}
</table>
<p class="meta">All cells ns/op. <em>(&gt;cap)</em> = projected over the 10&nbsp;s cell
budget (quadratic regime). Raw dated output:
<code>{html.escape(src)}</code>.</p>

<h3>3.3 Reading the results honestly</h3>
<div class="win">
<strong>KTf beats Viennot on 7 of 9 workloads, flat at every size.</strong>
At n&nbsp;=&nbsp;10⁶: pop-drain 60&nbsp;vs&nbsp;80, eject-drain 55&nbsp;vs&nbsp;77,
mixed 52&nbsp;vs&nbsp;75, concat-fold 594&nbsp;vs&nbsp;1001 (1.7×), concat-tree
1903&nbsp;vs&nbsp;2759, concat+pop interleave 111&nbsp;vs&nbsp;270 (2.4×), and the
persistent-fork rerun 41&nbsp;vs&nbsp;64&nbsp;ns/op (1.6×).  The model layer's
quadratic cells are gone, and the verified fusion pass (OpsFused.v) bought a further
20–30% on every removal path over the plain mirror.
</div>
<div class="honest">
<strong>Where we still lose: the two build-side workloads.</strong> Steady push
(113&nbsp;vs&nbsp;79) and steady inject (103&nbsp;vs&nbsp;86) trail by ~1.2–1.4×.
Both are dominated by one verified §4-deque push per element (~81&nbsp;ns
standalone); Viennot's hand-tuned buffer push is a few tens of ns cheaper inside
their cadeque.  Closing this means applying the same verified-fusion treatment to
the kt4 extraction's push path — a §4 concern, orthogonal to the catenable layer,
and the identified next target (along with the level-erasure data refinement that
would remove the per-element box).
</div>
<p><strong>The model baseline (KT) tells the same story from the other side.</strong>
Its cons-side cells (push/pop on a bare list) bound what any buffer can do, and its
quadratic inject/eject cells are the price the production artifact was built to
remove.  Both extremes bracket KTf exactly where the mechanized
buffer-primitive counts say it should sit.</p>

<h2>4 · Verdict</h2>
<table>
<tr><th>Dimension</th><th>Winner</th></tr>
<tr><td>Functional verification (totality + sequence semantics + invariant preservation, concat included)</td>
<td><strong>Parity</strong> — same theorem shape, both axiom-clean</td></tr>
<tr><td>Mechanized worst-case cost bound</td>
<td><strong style="color:var(--kt)">Ours only</strong> (<code>cat_wc_o1</code>)</td></tr>
<tr><td>Production wall-clock performance</td>
<td><strong style="color:var(--ktf)">Ours on 7 of 9 workloads</strong> (both drains,
mixed, all concats, forks — up to 2.4×); <span style="color:var(--vi)">theirs</span>
on build-side push/inject by ~1.2–1.4×</td></tr>
<tr><td>Toolchain footprint</td>
<td><strong style="color:var(--kt)">Ours</strong>: kernel + stdlib only ·
<span style="color:var(--vi)">theirs</span>: 3 plugin dependencies</td></tr>
<tr><td>Proof-text economy</td>
<td><strong style="color:var(--vi)">Theirs</strong> (~5× smaller cadeque theory)</td></tr>
</table>

<h2>5 · Reproduce</h2>
<pre><code>make bench-cadeque                              # full sweep, ~2 minutes
SIZES="1000 10000" bench/cadeque-compare.sh     # quick look
bench/render-comparison-page.py                 # regenerate this page</code></pre>

<footer>
Generated by <code>bench/render-comparison-page.py</code> from
<code>{html.escape(src)}</code>.
Companion report: <code>kb/reports/viennot-comparison-2026-06-11.md</code> ·
Keystone closure: <code>kb/reports/catenable-keystone-closure-2026-06-11.md</code> ·
Reference development: Viennot, Wendling, Guéneau, Pottier,
<em>Verified Catenable Deques</em> (vendored at
<code>external-refs/VerifiedCatenableDeque/</code>, MIT).
</footer>
</body>
</html>
"""

out = "kb/viennot-comparison.html"
os.makedirs(os.path.dirname(out), exist_ok=True)
open(out, "w").write(page)
print(f"wrote {out} ({len(page):,} bytes) from {src}")
