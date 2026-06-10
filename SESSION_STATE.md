# SESSION_STATE — rebuild (Phase 4b in progress)

## ★ OVERNIGHT MISSION (2026-06-03, second night) ★
PROGRESS-6 (this iteration): J v2 LANDED, CONCAT RE-CLOSED, 2 ADMITS LEFT
(cad_pop/eject_total_J_seq). Done: Color.v grew body_depth + the mutual
stored/cnode/cbody/chain_leveled family; J = chain_wf /\ chain_ends_green
/\ chain_leveled 0. WfLemmas: node_push/inject_leveled,
root_and_child_leveled, tree_of_leveled, push/inject_chain_leveled.
ConcatLemmas: cad_concat_total de-J'd (explicit wf/green conjuncts) + the
full colour-blind leveled companion chain (fold_push/inject, degenerate,
make_*_only, make_*, concat_small_*, cad_concat_leveled — all PROVEN, no
admits). Print Assumptions: empty/push/inject/concat closed under J v2.

★ POP/EJECT CAMPAIGN MAP v2 (decided this iteration — READ THIS) ★
DECISION: deep-green ("every inner terminal green") is NOT an invariant —
KT99 p.594 leaves paths from children of GREEN triples and nonpreferred
children of YELLOW triples unconstrained, and repair_front's SSmall path
legitimately leaves a red-topped child under the new green root v; a later
concat 1a wraps that red-top chain into an SBig. Hence stored children can
be red-topped and REPAIR'S CONCATS NEED A SEMIREGULAR CONCAT (Lemma 6.2's
weak half): SR-concat = chain_wf+leveled in, chain_wf+leveled+seq out, NO
ends_green anywhere. THE KEY FEASIBILITY INSIGHT (colour-mono saves it):
result-root colour rank >= old-root colour rank in every builder, and
chain_wf only demands greenness at (i) BPairO's parked lc, (ii) the BHole
root clause CG-or-CR-with-green-child. So per-old-colour SR bundles:
  - old CR (BHole red root, now allowed): red clause supplies FULL
    ends_green child — covers every obligation; result can be CR (only
    case) and its red clause re-discharges from the old one.
  - old CO: BPairO clause supplies parked-lc ends_green; result CO via
    BPairO re-parks an already-green lc; result CO via BSingle needs
    NOTHING (body clauses have no ends conditions).
  - old CY / old CG: result is CY/CG-ish (mono) -> body/root clauses
    need NOTHING green (CY/CO BSingle, BPairY have no ends clauses).
  - old CG WITH child has measures >= 8 -> result green outright; old
    CG childless goes through the op-fix eject2-lift branch whose
    singleton child self-supplies its greenness.
SR campaign pieces (A): make_left_only_sr, make_right_only_sr,
make_left_sr, make_right_sr, concat_small_{left,right}_sr (incl. big),
cad_concat_sr — mirror the proven J-versions, replacing root_child_facts
bundles with the per-colour table above; conclusions drop ends_green.
(B) pop_raw_total (and eject mirror), statement:
  J-style hyps (chain_wf + chain_ends_green + chain_leveled k) + c<>CEmpty
  -> exists x c', pop_raw c = Some (x,c') /\ stored_leveled k x /\
  chain_wf KOnly c' /\ chain_leveled k c' /\ seq c = seq x ++ seq c'.
  NO red-disjunct predicate needed: chain_wf c' itself forces the new
  terminal CG-or-(CR with green child) — repair dispatches on the
  computed colour. Facts that make it work: (a) red result root only
  from an ORANGE old root, whose BPairO/BSingle clauses + input top
  ends_green supply ends_green of the re-bundled child (tree_of CR case
  root_color_facts ✓); (b) post-pop sizes survive: rooted measures are
  >=6 pre-pop (G>=8/Y7/O6 — terminal green by input J, body heads Y/O)
  so >=5 after; childless violations are exactly the op's
  rebuild_childless (only) and Viennot collapse branches. COLLAPSE OP
  FIXED this iteration (fold-push into the KRight sibling broke its
  |p|=2 discipline): now re-crowns tree_of (Node KOnly (lp++ls++p2) s2)
  d2 over the peeled sibling root — new prefix = 4+2+2 = 8, so the min
  colour = old right-root colour key (gyor_of |s2|), and the per-colour
  facts come from root_child_facts of r (input J gives ends_green r);
  if rooted, |s2| >= 6 so never red; if d2 = CEmpty childless green.
  l' = CEmpty arm unreachable (childless KLeft keeps >= 5+2). NOTE pop_raw
  must be stated KIND-GENERICALLY (chain_wf kd c) because the CPair case
  recurses into the KLeft component; node sizes per kind; the CSingle
  with-child case has nonempty prefix (with-child only roots are
  two-sided; KLeft/KRight prefixes are 2 or >=5). (c) at k=0 the
  popped cell is stored_leveled 0 = SGround (cad_pop's match ✓); at
  child levels k+1 it is SSmall/SBig (repair's match ✓).
(C) repair lemmas: repair_front/back/both/packet/pop_side/eject_side.
  repair_front (red u=(p1,d1,s1), k-level, ends_green d1 from u's red
  clause => full J of d1 at level S k): pop_raw_total on d1 gives the
  cell; SSmall b: |b|>=3 => |p1++b|>=8 GREEN v, child d1' only needs
  chain_wf (green root clause) — fine red-topped ✓ no concat. SBig p2
  d2 s2: v green (|p1++p2|>=8); d3 := cad_concat_sr d2 (push_chain
  (SSmall s2) d1') — both args SR+leveled ✓ (push_chain_preserves_wf +
  push_chain_leveled). NO repair_both reorder needed: SR-concat
  tolerates red tops on both sides (drop the earlier reorder note).
  Result terminal v is GREEN => ends_green restored => J. levels: cell
  contents at k splice into u's k-buffers ✓ d2/s2 at S k ✓.
(D) assemble cad_pop_total_J_seq: pop_raw_total at k=0 (SGround ✓) then
  repair_pop_side: CEmpty trivial; CSingle repair_packet; CPair: repair
  left packet (right untouched keeps its J half). Mirror eject.
Recommended order: B first (self-contained, moderate), then A (the big
one), then C, then D. Keep every piece green+committed.
PROGRESS-5 (this iteration): CONCAT KEYSTONE CLOSED. Print Assumptions now:
cat_keystone_{empty,push,inject,concat} = "Closed under the global context".
ConcatLemmas.v = ZERO admits. Proven this round: make_left_total,
make_right_total (full right-side mirror stack: child_color_facts_mono /
right_rebuild_total / make_right_only_total / make_right_pair_core),
concat_small_left_big, concat_small_right_big (with only_push_rebuild_total /
only_inject_rebuild_total). OP FIX in Ops.v (concat_small_left/right, CSingle
branch, d2=CEmpty): childless only root carries no colour constraint so |s2|
could be 5 and the rebuilt min-coloured top was RED (J-violating; old admitted
statement UNPROVABLE). Fix: eject2 from p2 into the suffix (mirror: pop2 from
s1 into prefix) lifting the small side to >=7 => root CY/CG, absorbable.
Sequence-preserving, O(1), examples unchanged.
REMAINING = 2 admits, both CatKeystone: cad_pop_total_J_seq,
cad_eject_total_J_seq. POP/EJECT OBSTRUCTION MAP (read before attempting):
(1) LEVELS: cad_pop pattern-matches the popped cell against SGround; J v1
has no stratification, so a top root buffer could hold SSmall/SBig and
pop_raw would return a non-ground cell (cad_pop => None). Grow J in place
(Color.v): a level-indexed wf — top chain at level 0, root buffers hold
level-k stored where SGround only at k=0, SSmall b children at k+1, SBig p
c q's chain c at k+1. Mirror the deque keystone's well_leveled (depth-aware
packet_depth + k). DESIGN DECISION (do it this way): do NOT add a nat
parameter to the existing mutual fixpoints — that breaks every proven
lemma. Instead add a SEPARATE mutual fixpoint family
stored_leveled (k:nat) / cnode_leveled k / cbody_leveled k /
chain_leveled k (same recursion skeleton as the wf family) and grow J to
J d := chain_wf KOnly d /\ chain_ends_green d /\ chain_leveled 0 d —
exactly how the deque keystone composed I_kt. All existing wf/seq lemmas
stay untouched; add parallel *_preserves_leveled lemmas (push/inject/
concat/builders), which are mechanical because the ops move whole cells
between same-level buffers. Then ALL existing lemmas re-thread: builders move whole cells
between SAME-level buffers (k preserved); SSmall/SBig parking takes
level-k buffer contents into a level-(k) cell stored in a level-k buffer?
NO: parked cells go into the CHILD chain = level k+1, and their contents
came from level-k buffers => SSmall wraps a level-k buffer and sits in a
level-(k+1)... wait check: SSmall cell pushed into child chain d1 (level
k+1): the cell is a level-(k+1) stored whose buffer holds level-k? DESIGN
CAREFULLY against Model.v's stored_seq before writing. Sanity anchor:
cad_push pushes SGround at level 0; node buffers at level k hold stored of
level k; a node's child chain is level k+1; SSmall b at level k+1 holds b
whose elements are level-k stored (they came from a level-k buffer);
SBig p c q at level k+1: p,q level-k contents, c is a level-(k+1) chain?
NO — c came from root_and_child of a level-k tree => c is level k+1
already. So stored_wf (k+1) (SSmall b) := all (stored_wf k) b;
stored_wf (k+1) (SBig p c q) := all level-k p,q + chain_wf (k+1) c;
stored_wf 0 s := s is SGround. Verify against make_left_pair_core's cell
(SBig (s1++p2) d2 s2': s1,p2,s2' level-k buffers, d2 level-(k+1) child ✓✓).
(2) REPAIR'S CONCAT NEEDS J OF STORED CHILDREN: repair_front does
cad_concat d2 (push_chain (SSmall s2) d1') where d2 sits inside a popped
SBig — cad_concat_total needs J d2 = chain_wf /\ ends_green, but
stored_wf only records chain_wf. Options: (a) strengthen stored_wf with
chain_ends_green c for SBig — then check every SBig constructor site:
make_left_pair_core/make_right_pair_core build SBig with d2 := child of a
J-tree root via root_and_child — child ends_green holds for Y (BSingle:
packet-tail green = reassembled single's ends_green ✓) and O roots
(BPairO: parked lc ends_green ✓ + packet tail ✓) but FAILS for G roots
(child unconstrained) and BPairY parked rc (only chain_wf). So (a) also
requires strengthening chain_wf's green-root clause (ends_green rest) and
BPairY (ends_green rc) — i.e. EVERY child chain ends_green ('every path
green except a repairable top red'). That is a big but principled
refinement: re-check tree_of_wf/tree_of_ends_green (CY/CO splice moves the
old root INTO the body — body clauses unchanged), pkt_update_preserves
(strong version already threads ends_green), the weak *_preserves_wf
variants (may need upgrading to carry ends_green), root_color_facts (CR
clause already demands ends_green child), and all four builders' wf
obligations. Check Lemma 6.1/6.3 in kb/spec/section6-catenable-deques.md
(lines ~60-100) for what KT99 actually requires of stored sub-deques
before choosing. (3) pop_raw shape lemmas needed: pop_raw on J + seq<>[]
is Some; popped = head of cad_to_list; result semiregular with only the
pop-side terminal possibly red (define 'semiregular-after-pop' predicate
or reuse chain_wf + a weakened ends predicate); rebuild_childless
preserves wf/seq (one-sided merge); the CPair collapse branch (lp<5)
fold-pushes <=6 cells — fold_push_preserves exists in WfLemmas. (4)
repair_packet preservation: red terminal => ends_green rest (the red
clause) => pop_raw rest total via (3) at the child level; spliced node
sizes: |p1|=5 red + |p2|>=3 gives >=8 ... verify against §6 cases. Suggest
order: FIRST do the level clause (1) alone and re-thread (mechanical),
commit; THEN decide (2) reading the spec; THEN (3) pop_raw lemmas; THEN
(4); finally assemble cad_pop_total_J_seq and mirror eject.
PROOF-TOOL NOTES added this round: (a) cbn [allowlist] may refuse to
delta-unfold an op whose body starts with a stuck if — use
`unfold op. rewrite Hcond. cbn [fst snd].` (any allowlist cbn still does
iota, exposing match arms after destruct-eqn substitution); (b) destruct-eqn
substitutes in hypotheses too, so pose facts AFTER destruct then rewrite Hrc
in them; (c) `rewrite lemma` hits the LEFTMOST instance — pin with explicit
args (cchain_seq_pair (CSingle pl rl) ...); (d) child_color_facts is
DOWNWARD-monotone in gyor_rank (child_color_facts_mono) — the universal
bundle-key converter.
PROGRESS: admits 5 -> 3. PUSH AND INJECT FULLY CLOSED (cat_keystone_push/inject on
zero admits): WfLemmas now has gyor mono + receiver lemmas + pkt_update_preserves
(generic central assembly) + push/inject_chain_preserves. PROGRESS-4: make_left_only_total PROVEN (the 1c/1d builder). NEXT = make_left_total
(dispatch: CSingle root via root_two_sided-from-nondegenerate + root_child_facts
keyed at gyor_of(min)=node_color of root (node_color_measure); CPair: roots via
root_and_child_facts on both sides (kinds KLeft/KRight; sizes |p1|>=5,|s1|=2 /
|p2|=2,|s2|>=5); 1b (d1=CEmpty): make_left_only (p1++s1++p2) d2 s2 with bundle
keyed gyor_of(min(|p1++s1++p2|,|s2|)) — derive from t2's (right root's) colour:
min(>=9,|s2|)-colour = gyor_of |s2| = right-root colour ✓ root_child_facts of the
right tree (KRight root coloured by |s2| ✓ same measure!); sizes >=5 ✓ all-wf app;
seq: seq d = seq lt ++ seq rt with lt childless = bufp1++bufs1 (single_node_seq)
and rt = bufp2 ++ seq d2 ++ bufs2 (root_and_child_seq+node eq) — target
buf(p1++s1++p2) ++ seq d2 ++ bufs2 ✓ assoc. 1a (d1<>CEmpty): eject2 s2 (>=5);
SBig (s1++p2) d2 s2' wf (>=3/>=3 + chain_wf d2 + bufs wf); inject into d1 — SAME
colour-dispatch pattern as 1c but key = LEFT-root colour = gyor_of |p1| EXACTLY
(KLeft measure) so new node colour IDENTICAL to old (no mono needed); bundle from
root_child_facts of the left tree. THEN make_right_total mirror, THEN small-big
2/3. OLD: PROGRESS-3: buffer toolkit + child_color_facts/root_child_facts PROVEN. NEXT =
make_left_only_total (1c/1d on an only-triple's pieces (p1,d1,s1), both >=5,
bundle keyed on gyor_of(min |p1| |s1|) given only when d1<>CEmpty):
- 1d (d1=CEmpty): <=8: eject2 s1, node KLeft (p1++s1') [y;z] childless green;
  >8: s1=a::b::c::srest, eject2 srest, node over push (SSmall smid) CEmpty;
  both: chain_wf KLeft by explicit splits, ends CG, seq via eject2_inv+app.
- 1c (d1<>CEmpty): eject2 s1 -> SSmall s1' (>=3) injected: d1' =
  inject_chain d1 (SSmall s1'): wf via inject_chain_preserves_wf (KOnly);
  new node Node KLeft p1 [y;z] colour = gyor_of |p1| >=rank gyor_of(min) (mono);
  per new colour: CG ok; CY: cont CY d1': d1 CSingle-> use STRONG
  inject_chain_preserves (ends_green d1 = bundle-CY) -> ends d1'; d1 CPair->
  inject descends RIGHT so left unchanged: cont = ends left = bundle ✓;
  CO (only when bundle CO): facts parked-left (CPair: unchanged left, bundle) +
  cont CO d1' = ends (inject right) via STRONG inject on the right component
  (chain_wf KRight from CPair wf; ends right = bundle CO cont); CR impossible
  (rank >= bundle's >= 1). Seq: tree_of_seq + node eq + inject_chain_seq +
  eject2_inv. THEN make_left_total (dispatch CSingle via root facts incl.
  root_two_sided-from-nondegenerate; CPair 1a (eject2 s2, SBig (s1++p2) d2 s2'
  — note KLeft new node colour = OLD left-root colour literally, same |p1|)
  + 1b combined-only into make_left_only with min-colour bundle derived from
  t2's colour facts). THEN make_right mirror. THEN small-big Cases 2/3.
OLD: PROGRESS-2: concat ASSEMBLED — cat_keystone_concat discharged at keystone level;
keystone admits = 2 (pop, eject); concat sub-admits = 4 in ConcatLemmas.v:
concat_small_left_big / concat_small_right_big (Case 2/3 >=8: store the receiving
prefix/suffix as SSmall, push/inject into the root child via *_chain_preserves_wf
— NOTE the new outer node colour equals the old root colour by the §6 argument:
min(>=8, other-side) = other-side-determined; old root not red (terminal green by
ends_green / body-heads Y,O) so tree_of cases CG/CY/CO with cont_green from the
old terminal/parked facts — mirror pkt_update_preserves' case analysis) and
make_left_total / make_right_total (Case 1: subcases 1a-1d; sizes from J floors
make buf_eject2/pop2 succeed; built stored cells SSmall (>=3 from s1>=5 minus 2) /
SBig wf; inner inject via inject_chain_preserves_wf (k=KOnly fine); the result
node colour: new left node coloured by |p1| = OLD root colour (not red) — same
tree_of dispatch; ends_green of result via cont_green from old facts; SEQUENCE:
SBig/SSmall stored_seq unfold + buf_stored_seq_app + eject2/pop2 decompositions
(buf_eject2 b = Some (i,y,z) -> b = i++[y;z] -> buf seq splits) — add small
buf_eject2_seq/buf_pop2_seq lemmas first).
WAS: NEXT = obligation 2:
cad_concat_total_J_seq (case bash over cad_concat: degenerate_buf cases 2/3/4 +
make_left/make_right incl. only-variants; totality from J floors via buf_eject2/
pop2 on >=5 buffers; J of outputs via tree_of_wf — note tree_of here gets NEW
nodes (KLeft/KRight with fresh buffers) whose colour may be anything GREEN
(sizes >=8 outer per §6) — and sequence via SeqLemmas + buf_stored_seq_app +
stored_seq unfoldings of SBig/SSmall). Then obligation 3 (pop/eject; J grows
level clause).
Discharge the remaining Admitted obligations in rocq/KTDeque/Catenable/CatKeystone.v
down to ZERO admits with clean Print Assumptions (all 6 cat_keystone_* report
"Closed under the global context"). Order: (1) cad_push/inject_preserves_J — the
assembly mapped below under "REMAINING obligations" item 1 (toolkit already proven
in WfLemmas.v); (2) cad_concat_total_J_seq — case bash over cad_concat/make_left/
make_right (item 2); (3) cad_pop/eject_total_J_seq — EXPECT to grow J with the
level/stratification clause in Color.v IN PLACE (item 3; re-check empty_J,
singleton_J, and all prior discharges after the change; keep ONE invariant).
If 5 admits reach 0: add the cost layer (primitive-count counters mirroring the
frozen op code + constant bounds per op = cat_wc_o1), then point the gate script's
catenable profile at it. If stuck on an obligation after several honest attempts:
record the precise obstruction here + in kb/spec/catenable-concat-invariant.md,
ensure everything is committed green, and move to the NEXT obligation (or the cost
layer for already-discharged ops).

GUARDRAILS (same as the first night — do not violate):
- Branch `rebuild` only. NEVER push. Never leave the build broken: only commit
  when `eval $(opam env --switch=default 2>/dev/null); dune build rocq/KTDeque
  --display=quiet` exits 0 (per-file builds for iteration speed are fine).
- Use Admitted (never admit.) for any new scaffolding; net admits must not
  increase across a commit unless splitting one into strictly smaller precise ones.
- Refine J/chain_wf IN PLACE in Color.v — no candidate-predicate accretion.
- No destructive file operations. Additive proof work + in-place refinement only.
- Commit frequently; end every commit message with:
  Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>
- Update this file after each meaningful step (admit count, findings, next step).
- READ the "PROOF-STYLE NOTES (hard-won)" below before writing any tactic.
- Long builds: run dune in background (Bash run_in_background), never sleep-poll.
- If a heavy automation proof runs >5 min, kill it, revert to green, and use the
  structured/explicit style instead (216-case lesson from night one).


## PHASE 4b STATUS (2026-06-03)
DONE, committed green: kb/spec/catenable-type-design.md (design memo);
Catenable/Model.v (types: stored/cnode/cbody/cpacket/cchain + mutual sequence
semantics + examples); Catenable/Color.v (computed GYOR node_color, node_sizes
floors, the invariant J = chain_wf + chain_ends_green; empty_J, singleton_J).
J v1 deliberately omits level-stratification (recorded in-file; add in place if
an obligation demands it).

DONE also: Catenable/Ops.v with push/inject (colour-driven surgery via root_and_child/tree_of;
pkt_update = compose) AND concat (Cases 1-4 + 1a-1d, sequence-verified by vm_compute incl.
Case 1 CPair path). DONE also: pop/eject + §6 repair (Cases 1/2a-2c; pair-collapse via Viennot vector path;
drain-verified by vm_compute). DONE also: CatKeystone.v skeleton — cat_keystone_{empty,push,inject,concat,pop,eject}
proven from 7 Admitted obligations (functional keystone; empty already closed).
STATUS: 5 admits remain (cad_push/inject_seq DISCHARGED via SeqLemmas:
push_chain_seq/inject_chain_seq under chain_wf + chain_wf_root_prefix/suffix side
conditions + tree_of_seq/root_and_child_seq sequence-neutrality).
REMAINING obligations, in suggested order:
1. cad_push/inject_preserves_J — TOOLKIT NOW PROVEN (WfLemmas.v:
   root_and_child_facts / tree_of_wf / cont_green / tree_of_ends_green).
   Remaining assembly: (a) node_push/node_inject preserve node_sizes+cnode_wf
   (sizes only grow; stored_wf of the pushed element needed for cnode_wf —
   SGround trivially wf); (b) new-colour classification under old facts: old
   head CY/CO (body) or CG (terminal, from ends_green) => new colour in
   {CG,CY,CO} and new-CO only from old-CO (so the parked-left-green side fact
   carries over from root_color_facts); new-CR impossible; also new colour CO/CY
   => cont_green side facts from old cbody/ends_green (flip case: orange parked
   left WAS green; stuck cases: same terminal). (c) push_chain_preserves by
   induction (CEmpty k=KOnly hyp; CPair-left via ends_green of both sides; CSingle
   via the toolkit). Note k <> KRight for push (KLeft for inject) — receiving
   node sizes would break otherwise; call sites only use KOnly/KLeft (resp
   KOnly/KRight).
   PROOF-STYLE NOTES (hard-won): never full-cbn hyps containing node_color (form
   desync); use cbn allowlists ([chain_wf cbody_wf body_out_kind is_single],
   [chain_has_node], [node_color negb]); Rocq-9 destruct-eqn substitutes in
   HYPOTHESES too (no rewrite-in-hyp needed after destruct); close clauses with
   conversion-driven exact; explicit bullets per sub-branch (chained
   try-congruence can close bullets early).
2. cad_concat_total_J_seq — totality: every option arm Some under J (buf_eject2/
   pop2 sizes from J floors; make_left/right case-by-case); J of outputs (tree_of
   J-rebundling + the new node sizes per case — 1a/1c stored >=3 etc.); sequence
   via SeqLemmas + buf_stored_seq_app (stored_seq of SBig/SSmall unfold).
3. cad_pop/eject_total_J_seq — HERE J grows the level clause: popped element
   SGround needs stratification (add stored_level-style Prop to J in Color.v, in
   place; re-check empty_J/singleton_J and prior discharges). Repair totality:
   red terminal => child nonempty (colour def) => pop_raw Some; repair J: spliced
   node green (>=8 sizes per §6 Lemma 6.4); repair seq via SeqLemmas + concat seq.
THEN cost layer + gate. REMAINING for 4b (orig): (a) DISCHARGE the 7 obligations (expected: J grows the level/
stratification clause at pop-totality — SGround-ness is level-0; push/inject seq
needs J sizes for the empty-prefix suffix-push case; tree_of/root_and_child seq
lemmas are the workhorses — prove cchain_seq (tree_of n c) = cnode_seq n (cchain_seq c)
and the root_and_child inverse first); (b) then the COST layer: primitive-count
counters mirroring the frozen op code + constant bounds => cat_wc_o1; (c) gate:
point the catenable gate profile at cat_wc_o1. Old note: CatKeystone.v (cat_wc_o1 from admitted
obligations: J-preservation for all 5 ops, totality of the option-returning concat/pop/eject
under J, sequence correctness, primitive-count bound).

OLD design note for push/inject (KT99 Lemma 6.1 made
structural — the path surgery):
- push onto CEmpty => singleton only-triple.
- push onto CSingle (Pkt body n) rest: the receiving node = head of body (or n
  if body=BHole); push onto its prefix (suffix if prefix empty). Colour
  transitions change the PATH DECOMPOSITION (KT99: "adds t to or deletes t from
  the front of a preferred path"):
  * Y->G (head body node becomes green): SPLIT the packet — head becomes its
    own green packet: CSingle (Pkt BHole t') (CSingle (Pkt body_rest n) rest).
  * O->Y (head was BPairO t lc b'): preference flips right->left. New preferred
    continuation = INLINE the parked green-left chain lc = CSingle (Pkt lb ln)
    lrest: new packet = Pkt (BPairY t' lb) ln over lrest; the OLD continuation
    becomes the parked RIGHT chain = CSingle (Pkt b' n) rest. (Yellow's
    nonpreferred child needs no green condition — checked, clause 2 is
    orange-only.)
  * G stays G / Y stays Y / O stays O: in-place buffer push, no surgery.
  * Top node green that becomes... push on a GREEN top only adds elements =>
    >=8 stays >=8?? push INCREASES sizes: G stays G; Y(7)->G(8); O(6)->Y(7);
    R(5)->O(6) (red top can't occur under J's chain_ends_green at top).
  So push transitions are colour-INCREASING (toward green) — the easy
  direction; pop/eject decrease and trigger the red repair.
- Helpers to write first: node_push/node_inject (buffer-level), packet head
  access, the Y->G split and O->Y flip as named functions; then push/inject;
  Lemma 6.1 analogue = push preserves J (semiregular/regular split per KT99).
- THEN concat (Cases 1-4; constant element moves), THEN pop/eject repair
  (Cases 1, 2a-2c — uses concat recursively at the child level per KT99 Case
  1a! NOTE: KT99 pop-repair Case 1a calls CATENATE on child deques (d2 and
  d1''): the repair is NOT concat-free. cost story still constant: one level,
  constant catenations).
- Keystone: CatKeystone.v cat_wc_o1 from admitted obligations (rule 6).

Running unattended (user asleep) to progress the rebuild plan. Read this first.

## PHASE 2 (re-curation) DONE 2026-06-03
Non-canonical variants removed from rebuild (preserved on archive, pushed): rocq
Cadeque6/7/8/9 + Buffer6 + Public + catenable extractions; OCaml experimental lib
+ 24 catenable benches + viennot_cad + catenable tests/examples; Makefile/gate-script
catenable targets (catenable profile now SKIPs with archive pointer). All green:
rocq, ocaml, runtest, C check, 4 gate profiles, keystone gate 4/4. release-gate
anchors deque-keystone-gate.
NEXT = Phase 4b (catenable, fresh KT99 §6/Viennot build). First design task (do in
a FRESH focused session, paper-first like 4a): the Rocq type encoding of §6's
non-uniform recursion (triple = prefix/middle/suffix where the middle deque's
elements are STORED TRIPLES) + GYOR colours + preferred paths + the compressed
forest (adoptive pointers) for O(1) topmost-red access. Then J + cat_wc_o1 stated
top-down from admitted obligations (methodology rule 6). Mine
external-refs/VerifiedCatenableDeque (Color/GYOR.v, Cadeque/) for design only.

## ★★★ PHASE 4a CLOSED (2026-06-03) ★★★
`rocq/KTDeque/DequePtr/DequeKeystone.v`: **ZERO admits**; `deque_wc_o1_{push,inject,pop,eject}`
all report **Closed under the global context**. The unconditional WC-O(1) deque keystone is
proven (totality + I_kt preservation + one-repair cost bound; empty ⊨ I_kt; push/inject take
E.level x = 0). Whole rocq/KTDeque theory builds green. Mission item 1 DONE; item 2 (RBR) DONE.
NEXT (mission item 3, only if continuing): catenable Phase-4 per kb/spec/catenable-concat-invariant.md
— this is a LARGE fresh build (KT99 §6/Viennot GYOR structure); prefer to leave for the user's
review of the keystone unless instructed otherwise. Remaining small follow-ups instead:
(a) point a minimal gate at deque_wc_o1_* (+ keep frontier greps out), (b) consider linking
green-calls bound to NF_PUSH_PKT_FULL in DequeKeystone's Print Assumptions block.

## Branch / build
- Work ONLY on branch `rebuild`. Do NOT push (push needs human approval).
- Build: `eval $(opam env --switch=default 2>/dev/null); dune build rocq/KTDeque/DequePtr/DequeKeystone.vo` (and `dune build rocq/KTDeque` for the whole theory).
- `dune` is at `/home/yann/.opam/default/bin/dune`; `make` does NOT see it (it uses /bin/sh) — call `dune` directly after sourcing opam env.

## Mission (in priority order)
1. **Close Phase 4a — the deque keystone** in `rocq/KTDeque/DequePtr/DequeKeystone.v`. Discharge the remaining `Admitted` obligations until zero admits + clean `Print Assumptions` on `deque_wc_o1_{push,inject,pop,eject}`.
2. If 4a closes: finish `rocq/KTDeque/RBR/Succ.v` (close the one `Abort.`) — decision #2.
3. If those close: begin the catenable Phase 4 proof work per `kb/spec/catenable-concat-invariant.md` (§6/Viennot GYOR) — additive only.

## Current state (as of start)
- `DequeKeystone.v` compiles. `deque_wc_o1_*` proven modulo **5 admits**:
  - `I_kt_implies_kt4_total_state` (totality core)
  - `push/inject/pop/eject_kt4_preserves_I_kt` (preservation)
- 4 totality obligations already discharged (Qed) by reducing to the single lemma above via existing infra.
- Invariant: `I_kt c := regular_kt_top c /\ colors_consistent c /\ well_leveled c` (see `kb/spec/deque-reachable-invariant.md`).

## The crux to solve
The residue is **recursive green-readiness / repairability** (the KT cascade bound):
- `kt4_total_state`'s Green clause needs `yellow_wrap_pr_total_pre tail` = (tail Red-headed ⇒ `green_of_red_k tail = Some`).
- `green_of_red_k_ready_at` Case 2 (Hole-inner red over a `KCons` tail) needs the tail's buffers **green-shaped**, not just not-red.
- Hypothesis to encode in `colors_consistent`: every link's tail is "green-ready" — a `Hole`-inner link's tail is Green-headed (green buffers) or `Ending`; and every red-headed tail is repairable. Make this RECURSIVE.
- Then `I_kt_implies_kt4_total_state` should follow via `green_of_red_k_total_under_ready_levels`. The hard part shifts to **preservation** (the 4 `*_preserves_I_kt`): the green-ready clause must survive push/inject (green→yellow at same depth) and the `green_of_red_k` repair (Case 1/2 produce green heads; Case 3 produces a green head over a fresh red inner — check it stays repairable) and pop/eject.

## Reuse (do NOT reprove these — they exist + are audited)
- `green_of_red_k_total_under_ready_levels`, `green_of_red_k_case{1,2,3}_total_under_levels`, `green_of_red_k_ready_at`, `green_of_red_k_context_ready_at`, `green_of_red_k_ready_at_from_context` (PublicTheorems.v).
- `kt4_total_state_{push,inject,pop,eject}_pre`, `{push,inject,pop,eject}_kt4_total_under_pre` (totality plumbing — already wired in DequeKeystone).
- `{push,inject,pop,eject}_kt4_preserves_regular_top` (the regular_kt_top half of preservation — REUSE for the regular component).
- `{push,inject,pop,eject}_kt4_green_calls_le_1` (cost — already wired).
- Model.v: `buf_all_at_level`, `packet_levels`, `chain_levels`.
- Element is concrete `ElementTree` (Model.v:61) — positive-level elements unpair (a theorem); use it for `well_leveled`'s unpairability needs.

## METHODOLOGY / GUARDRAILS (do not violate)
- **Top-down with tracked admits** (rebuild plan rule 6): use `Admitted` (never `admit.`). The admit set is the to-do list via `Print Assumptions`.
- **Never leave the build broken.** Only `git commit` when `dune build rocq/KTDeque/DequePtr/DequeKeystone.vo` exits 0. If an edit breaks the build and you can't fix it quickly, `git checkout -- <file>` to revert and try a different approach.
- **Net admits must not increase** across a commit unless a big admit is split into strictly smaller, precisely-stated ones.
- **One invariant, refine in place.** Do NOT spawn many named candidate predicates (that is the accretion anti-pattern that failed before). Refine `colors_consistent` / `I_kt` directly.
- **No destructive operations.** Do NOT delete files, do NOT do the Phase-2 re-curation (removing Cadeque variants) — that needs human go-ahead. Additive proof work only.
- **Commit frequently** with descriptive messages; end every commit message with:
  `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`
- Update this SESSION_STATE.md after each meaningful step (admit count, what changed, next step) so progress survives context resets.
- If genuinely stuck on the green-readiness invariant after several honest attempts, do NOT churn: record the precise obstruction in `kb/spec/deque-reachable-invariant.md` + here, make sure everything is committed green, and move to mission item 2 (RBR) so the night is still productive.

## make_small_preserves_levels roadmap (mapped 2026-06-03)
Target: `make_small b1 b2 b3 = Some c -> buf_all_at_level k b1 -> buf_all_at_level (S k) b2 -> buf_all_at_level k b3 -> chain_levels k c`. (Then `green_of_red_k` Case 1 = `chain_to_kchain_g`, which preserves levels — needs a trivial `chain_to_kchain_g` level lemma since it only adds Green tags; well_leveled_at k c <-> chain_levels k (kchain_to_chain c), and kchain_to_chain (chain_to_kchain_g c) = c.)
9 cases (prefix_decompose b1 x suffix_decompose b3). Reuse EXISTING (do not reprove):
- `pair_each_buf_after_halve_preserves_levels` (PublicTheorems.v:12127) + `..._total_under_levels` (7241) — Overflow/Overflow case.
- `suffix_rot_unpair_total_under_levels` (7279), `prefix_rot_unpair_total_under_levels` (7305) — Underflow/Overflow + Overflow/Underflow.
- `make_small_total_under_levels` (7331) — existence (pattern to mirror).
- `make_small_chain_to_kchain_g_context_ready` (7452) — shows the output-shape reasoning per case (mirror its case structure).
Need NEW trivial level lemmas: `prefix23` (OpsKT.v:273), `suffix23` (280), `suffix12` (288), `mk_ending_from_options` (594), `buffer_unsandwich` (349), `buffer_push_chain`/`buffer_inject_chain` level-preservation, `buf5_push_naive`/`buf5_inject_naive`/`buf5_pop_naive`/`buf5_eject_naive` (have `buf5_*_preserves_levels` in OpsAbstract.v 211-243). Most simple cases close by cbn + the E.unpair_level/E.level_pair facts (pattern as in `prefix_concat_preserves_outer_green_levels` proof, PT:6512).

## make_small_preserves_levels — ATTEMPT NOTE (2026-06-03)
A uniform automation that ALSO destructs b2 into 6 => 216 cases x heavy tactics (repeat constructor + lia + E.level_pair rewrites) ran >5 min without finishing — too slow, reverted. DO NOT destruct b2. Instead: `unfold make_small in Hmake`, destruct b1+b3 (36 cases), and in each case handle b2's ONE operation via its helper lemma WITHOUT destructing b2:
  - (underflow,underflow): `buffer_unsandwich b2` -> `buffer_unsandwich_levels`.
  - (underflow,ok)/(ok,underflow): `buf5_pop_naive`/`buf5_eject_naive b2` -> `buf5_pop/eject_preserves_levels` (OpsAbstract); `buf5_push/inject_naive` -> `buf5_push/inject_preserves_levels`.
  - (underflow,overflow)/(overflow,underflow): `suffix_rot`/`prefix_rot` -> `suffix_rot/prefix_rot_preserves_levels`, then `E.unpair` -> `element_unpair_at_s_levels`.
  - (ok,ok): output `ChainCons (PNode p1' Hole s1') (Ending b2)` directly; p1'/s1' are b1/b3 (level k), b2 level (S k).
  - (ok,overflow)/(overflow,ok): `buffer_inject_chain`/`buffer_push_chain b2 (E.pair ..)` -> `buffer_*_chain_levels` (the pair is level S k).
  - (overflow,overflow): `buffer_halve` + `pair_each_buf` -> `pair_each_buf_after_halve_preserves_levels`; `suffix12` -> `suffix12_levels`.
  Each case: get the component levels from the helper, then prove chain_levels via constructors + `prefix23_levels`/`suffix23_levels`/`mk_ending_from_options_levels`. Keep buffer ops folded with `cbn -[E.pair E.unpair buffer_unsandwich buf5_pop_naive buf5_eject_naive suffix_rot prefix_rot buffer_halve pair_each_buf buffer_push_chain buffer_inject_chain]`. This is ~9 distinct case bodies, fast.

## make_small_preserves_levels — FOUNDATION COMPLETE (2026-06-03)
All 10 helper level lemmas proven (Qed) in DequeKeystone.v: `prefix23_levels`, `suffix23_levels`, `suffix12_levels`, `mk_ending_from_options_levels`, `buffer_push_chain_levels`, `buffer_inject_chain_levels`, `buffer_unsandwich_levels`, `suffix_rot_preserves_levels`, `prefix_rot_preserves_levels`, `element_unpair_at_s_levels`. Plus existing reuse: `pair_each_buf_after_halve_preserves_levels` (PT:12127), `buf5_{push,inject,pop,eject}_preserves_levels` (OpsAbstract:211-243), `E.unpair_level`/`E.level_pair`.
ASSEMBLY RECIPE for `make_small_preserves_levels` (forall k b1 b2 b3 c, level k b1 -> level (S k) b2 -> level k b3 -> make_small b1 b2 b3 = Some c -> chain_levels k c):
  `unfold make_small in Hmake`; destruct b1, b3 (prefix/suffix_decompose). For the 9 (pre-decomp x suf-decomp) cases, the inner matches in Hmake on `buffer_unsandwich b2` / `E.unpair _` / `Nat.eq_dec` / `suffix_rot`/`prefix_rot`/`buffer_halve`/`pair_each_buf` give the output; `destruct (E.unpair ..) eqn:Hup; [|discriminate]` then use `element_unpair_at_s_levels` for the pair levels (need `E.level elem = S k` from `buffer_unsandwich_levels`/`buf5_pop/eject_preserves_levels`/`suffix_rot/prefix_rot_preserves_levels`); `injection Hmake` to get c; then prove `chain_levels k c` via the matching helper (`mk_ending_from_options_levels` / `prefix23_levels`+`suffix23_levels` for the PNode-Hole cases / `buffer_push_chain_levels`/`buffer_inject_chain_levels` for Ok/Overflow / `suffix12_levels`+`pair_each_buf_after_halve_preserves_levels` for Overflow/Overflow). Then `green_of_red_k_preserves_well_leveled` Case 1 = `chain_levels k (make_small ...)` lifted through `chain_to_kchain_g` (trivial: adds Green tags; need `chain_to_kchain_g_well_leveled : chain_levels k c -> well_leveled_at k (chain_to_kchain_g c)`, by induction on c).

## Progress log (newest first)
- 2026-06-03 iter (REPAIR PRESERVATION FULLY CLOSED): PROVED make_small_colors_consistent (structural, no level premises) + green_prefix/suffix_concat_green_shapes + prefix/suffix_concat_outer_green_shape + green_of_red_k_preserves_colors_consistent. Combined with green_of_red_k_preserves_well_leveled, the bounded repair now provably preserves the FULL invariant payload (colours + levels). Build green, 4 admits.
  FINAL STRETCH (the 4 *_preserves_colors_leveled admits): per-op case analysis mirroring the *_total proofs. Arms:
  * KEnding arms: outputs KEnding or KCons Green (B3 Hole B3) (KEnding B0) — structural cc + levels (level-0 elements: push x has E.level x = 0... CAREFUL: preserves lemmas don't have the E.level x = 0 hypothesis! KEnding push B5->Green-split needs buf levels at 0 from well_leveled + pushed x at 0 — MUST add E.level x = 0 to push/inject_kt4_preserves_colors_leveled signatures (mirroring *_total) and thread through push/inject_kt4_preserves_I_kt + deque_wc_o1_push/inject (already have Hx there).
  * Yellow non-overflow arms: buffer +/-1 stays not-red (B1..B3 -> B2..B4 etc.); packet_levels of modified packet (buf5 facts); tail unchanged (cc_tail_color Yellow + cc + wl tail all unchanged).
  * Yellow B4/B1 repair arms: output = green_of_red_k (KCons Red (PNode modified i suf) tail): build cc of that red chain (cc_color_shape Red = I; cc_yellow_run i inherited; cc_tail_color Red tail from input's cc_tail_color Yellow tail (same: tc=Green); cc tail) + wl of it (packet_levels with modified buffer: B5 from B4+x — needs E.level x = 0; B0 from B1-drop ✓) then apply BOTH repair-preservation lemmas.
  * Green arms (yellow_wrap_pr): output KCons Yellow (PNode pre' i suf) tail' where tail'=tail (non-red top) or repaired tail. cc: Yellow shapes (pre' = green+1/-1 = not-red ✓ B4 or B1..); cc_yellow_run i ✓; cc_tail_color Yellow tail': tail Green/Ending => unchanged tc ✓; tail Red => tail' = repaired, top Green (green_of_red_k_top_green, OpsKTRegular:288) ✓; cc tail' via repair-cc lemma; wl tail' via repair-wl lemma (NOTE: repaired at index packet_depth+k — wl input gives tail at that index ✓ same k passes through).
  * Will need a yellow_wrap_pr_preserves lemma first: forall pre' i suf tail k, (premises: packet_levels k (PNode pre' i suf), shapes pre'/suf not-red?? wait yellow link needs not-red shapes of pre' AND suf — suf is the GREEN link's old suf (green => not-red ✓), cc_yellow_run i, cc_tail_color Green->… the input link was GREEN: cc_tail_color Green tail (tc <> Yellow); for output Yellow link need cc_tail_color Yellow tail' (tc' = Green): tail Green-top => ✓; tail KEnding ✓; tail Red-top => repaired Green-top ✓ — all cases OK) -> yellow_wrap_pr pre' i suf tail = PushOk c' -> colors_consistent c' /\ well_leveled_at k c'.
- 2026-06-03 iter (DESIGN FIX: tail-colour discipline): The Hole=>tail_green_ready clause was TOO STRONG — green_of_red_k Case 3 outputs Green-over-fresh-Red with non-green inner buffers (the prior accretion's exact *_not_push_closed counterexample). Refined colors_consistent IN PLACE: new `cc_tail_color col tail` clause (Yellow/Red links over Green-or-Ending; Green over non-Yellow; Yellow top-only); `tail_green_ready` now DERIVED via `tail_green_ready_of_cc` for col<>Green. context_ready/ready_at_of_consistent gained `col <> Green` premise (call sites: eapply with [| exact Hcc | exact Hwl]; discriminate — evar ordering). ALL existing proofs survive. Build green, 4 admits.
  ANALYSIS (verified on paper, record for the colours-preservation proof):
  * Case-1 outputs (chain_to_kchain_g of make_small): all links Green with structurally green buffers (prefix23/suffix23 = B2/B3; BD_*_ok/overflow kept bufs = B2/B3); depth-2 case inner = suffix12/B1 not-red; tails Green-or-Ending => cc holds UNCONDITIONALLY given success. Lemma: make_small_colors_consistent (no level premises; needs prefix_decompose_shapes/suffix_decompose_shapes + prefix23/suffix23/suffix12 shape lemmas + buffer_push/inject_chain cc lemmas).
  * Case-2 output Green link: shapes from green concat lemmas ✓; cc_yellow_run inner: pre2'/suf2' NOT-RED needs new lemma green_prefix_concat_green_b2_not_red (b2 green premise from derived tail_green_ready of the input RED link); cc_yellow_run child + cc_tail_color Green c2 (c2 non-Yellow) + cc c2 INHERITED from input tail link's cc.
  * Case-3 output: Green-over-Red ✓ legal now; R's cc_tail_color Red c1 inherited from input red link's cc_tail_color; cc_yellow_run child inherited.
  * Op-level: push Yellow keeps tail (cc_tail_color Yellow unchanged); push Green -> yellow_wrap_pr outputs Yellow over (tail-or-repaired): repaired is Green-topped (green_of_red_k_top_green, OpsKTRegular:288) ✓; pre'=B4 not-red, suf green=>not-red ✓.
- 2026-06-03 iter (MAJOR: repair level-preservation PROVEN): (a) Fixed well_leveled_at to DEPTH-AWARE tail index `packet_depth p + k` (naive S-k-per-link was FALSE for nested packets; Model.v chain_levels has the same bug — do not use it; use new chain_levels_d). (b) PROVED `make_small_preserves_levels` (goal-carried style: keep Hmake in goal so destructs abstract it — in-hyp rewrites fail under match binders; ms_reduce Ltac keeps blocks folded). (c) PROVED `green_of_red_k_preserves_well_leveled` (3 cases; Case-3 needs colors_consistent for not-red shapes; depth bookkeeping via well_leveled_at_eq+lia; gotcha: re-`cbn in Hwltail` after destructing i1 or lia sees mismatched packet_depth atoms). Also: chain_to_kchain_g_well_leveled, well_leveled_at_eq, prefix/suffix_decompose_levels. Imports added: Buf5Ops, OpsAbstract. Build green, 4 admits.
  NEXT: op-level well_leveled preservation: prove `push_kt4_preserves_well_leveled`-style facts by case analysis mirroring the *_total proofs (non-repair arms: buffer changes only — need packet_levels of modified packet, easy from buf5 facts; repair arms: green_of_red_k_preserves_well_leveled, noting yellow_wrap_pr wraps result in KCons Yellow + the repair is applied to (KCons Red (PNode modified-buffer i suf) tail) so need colors_consistent of THAT red chain — the cc clauses for Red links are permissive ✓, only cc_yellow_run i + Hole=>tail_green_ready needed, inherited from input). THEN the colors_consistent half (green_of_red_k_preserves_colors_consistent — outputs green-headed; Case 3 fresh Red inner; needs tail_green_ready of outputs), then assemble the 4 *_preserves_colors_leveled admits.
- 2026-06-03 iter (rot + unpair-levels): proved `suffix_rot_preserves_levels`, `prefix_rot_preserves_levels`, `element_unpair_at_s_levels`. make_small foundation now COMPLETE (10 helpers). Build green, 4 admits. Next: assemble `make_small_preserves_levels` per the recipe above.
- 2026-06-03 iter (buffer-chain/unsandwich): proved `buffer_push_chain_levels`, `buffer_inject_chain_levels`, `buffer_unsandwich_levels` (Qed, build green, 4 admits). FINDING: `suffix_rot_unpair_total_under_levels`/`prefix_rot_unpair_total_under_levels` (PT:7279/7305) give only EXISTENCE of the unpair, NOT output levels — so make_small Overflow cases need NEW `*_preserves_levels` rot lemmas. They ARE derivable: the paired input is level `S k`, suffix_rot/prefix_rot keep level `S k`, and `E.unpair_level` gives the unpaired pair at level `k` (and `center` level `S k`). NEXT: prove `suffix_rot_preserves_levels`/`prefix_rot_preserves_levels` (output: cd_paired/ab_paired level `S k` so unpair gives level-k pair via E.unpair_level; center level `S k`), then assemble `make_small_preserves_levels` (9 cases, mirror `make_small_total_under_levels` PT:7331 structure), then `green_of_red_k_preserves_well_leveled`.
- 2026-06-03 iter (helper lemmas): proved 4 simple make_small helper level lemmas in DequeKeystone.v (Qed): `prefix23_levels`, `suffix23_levels`, `suffix12_levels`, `mk_ending_from_options_levels`. Build green, 4 admits. NEXT: buffer-op level lemmas (`buffer_unsandwich`, `buffer_push_chain`/`buffer_inject_chain` preserve levels; `buf5_*_naive` reuse OpsAbstract `buf5_*_preserves_levels`), then assemble `make_small_preserves_levels` (9 cases) reusing `pair_each_buf_after_halve_preserves_levels`/`suffix_rot`/`prefix_rot_unpair_total_under_levels`.
- 2026-06-03 iter (RBR + frontier map): closed RBR/Succ.v Abort (was a wrong-valued example on irregular input; replaced with correct `succ_rec_five_irregular` reflexivity). RBR now zero Abort/admit (mission item 2 DONE). Confirmed deque preservation reuse: `prefix_concat_preserves_outer_green_levels` (PublicTheorems 6503) and `suffix_concat_preserves_outer_green_levels` (6534) give green-shape + level-k/(S k) of concat outputs — directly usable for `green_of_red_k_preserves_well_leveled` Cases 2/3. GAP: Case 1 uses `make_small` (9 sub-cases) and has NO ready output-level lemma — need a new `make_small_preserves_levels` (assemble from buffer-op level facts like the concat ones; pattern as in `prefix_concat_preserves_outer_green_levels`'s proof: destruct all buffer shapes, use `E.unpair_level`/`E.level_pair`). So well_leveled half = {Case2/3 ready, Case1 needs make_small level lemma}; colours half still the harder wall. NEXT deque iteration: write `make_small_preserves_levels`, then `green_of_red_k_preserves_well_leveled`, then op-level well_leveled preservation, then colours.

- 2026-06-03 start: 5 admits in DequeKeystone.v. Totality reduced to `I_kt_implies_kt4_total_state`. Crux = recursive green-readiness.
- 2026-06-03 iter: refined `colors_consistent` with `cc_color_shape` + `tail_green_ready` (Hole-inner link => green/Ending tail). Proved 4 helper lemmas (Qed): `context_ready_of_consistent`, `ready_at_of_consistent`, `green_of_red_k_some_of_consistent`, `yellow_wrap_pr_total_pre_of_consistent`. Build green; still 5 admits (machinery, not yet wired to discharge).
- KEY FINDING: `kt4_total_state`'s B4 repair clauses are `forall x` (any level), but the existing totality lemmas need `E.level x = k`. `prefix_decompose (B5 x a b c d) = BD_pre_overflow (B3 x a b) c d` => the overflow pair is `(c,d)` (original B4, level k), x is kept; so `green_of_red_k` succeeds regardless of x. Public `push_kt4` is only ever called at the top with a level-0 element.
- DECISION: do NOT prove `I_kt_implies_kt4_total_state` (forall-x blocks it). Instead reprove the 4 `*_total` lemmas DIRECTLY using the helpers, adding `E.level A x = 0` to push/inject (faithful: public pushes level-0); pop/eject need no x. Then DELETE `I_kt_implies_kt4_total_state` and thread `E.level x = 0` through `deque_wc_o1_push`/`deque_wc_o1_inject`.

## STATUS 2026-06-03 (totality CLOSED)
- DequeKeystone.v builds green with **4 admits**: only `push/inject/pop/eject_kt4_preserves_I_kt`.
- All 4 `*_total` lemmas proven DIRECTLY (push/inject carry `E.level x = 0`; threaded through `deque_wc_o1_push`/`_inject`). `I_kt_implies_kt4_total_state` DELETED. `deque_wc_o1_*` each depend only on their `*_preserves_I_kt`.
- Helpers (Qed, reusable): `context_ready_of_consistent`, `ready_at_of_consistent` (free pre'/suf'), `green_of_red_k_some_of_consistent`, `yellow_wrap_pr_total_pre_of_consistent`.

## STATUS 2026-06-03 (4 admits — colour+level preservation only)
DequeKeystone.v green with exactly 4 admits: `push/inject/pop/eject_kt4_preserves_colors_leveled`
(`I_kt c -> op = result -> colors_consistent c' /\ well_leveled c'`). Everything else closed:
totality (direct), cost (`*_green_calls_le_1`), regular_kt_top preservation (reused), and the
`*_preserves_I_kt` wrappers (Qed). `deque_wc_o1_*` depend only on these 4.

### Reusable-lemma map for preservation (surveyed 2026-06-03)
- well_leveled half: `OpsAbstract.v` has `buf5_{push,inject,pop,eject}_preserves_levels` (211-243) and `{push,inject,pop,eject}_chain_preserves_levels` (253-336) — but those are for the abstract `Chain`, and there is NO ready `push_kt4 <-> push_chain` refinement via `kchain_to_chain` (only `kt4_packet_chain_view` relation + endpoint-only `push_chain_full (kchain_to_chain (KEnding b)) = ...`). So well_leveled must be proved DIRECTLY. The buffer-concat LEVEL lemmas to assemble `green_of_red_k_preserves_well_leveled` are in PublicTheorems.v: `prefix_concat_total_under_levels`/`suffix_concat_total_under_levels` (existence), `prefix_concat_preserves_outer_green_levels` (6503), `suffix_concat_preserves_outer_green_levels` (6534), `green_prefix_concat_preserves_green_outer_not_red_inner_levels` (7045), `green_prefix_concat_success_preserves_green_outer_levels` (7077), suffix duals (7109,7141), `..._from_not_red` (7173,7207), and `make_small_total_under_levels`. `green_of_red_k_case3_total_under_levels` (6479) shows the assembly pattern (uses prefix/suffix_concat_total_under_levels). Build `green_of_red_k_preserves_well_leveled` (3 cases) from these, then op-level via case analysis mirroring the `*_total` proofs (non-repair cases use `buf5_*_preserves_levels`).
- colours half: `green_of_red_k_top_green` (OpsKTRegular.v:288), `green_of_red_k_preserves_regular` (456), `kchain_top_color_chain_to_kchain_g_not_red` (PublicTheorems 10585), `make_small_chain_to_kchain_g_context_ready` (7452) — Case 1/2 outputs green-headed; Case 3 outputs `KCons Green (PNode .. Hole ..) (KCons Red ..)` (fresh red inner). Need bespoke `green_of_red_k_preserves_colors_consistent` showing the output satisfies `cc_color_shape`/`cc_yellow_run`/`tail_green_ready`. THIS is the prior wall.

### How to attack `*_preserves_colors_leveled` (the wall)
No pre-built level/colour preservation for the ops — bespoke. Plan:
1. **well_leveled** half first (more mechanical): prove `green_of_red_k c = Some c' -> well_leveled_at k c -> well_leveled_at k c'` and `yellow_wrap_pr pre i suf c = PushOk c' -> (levels of pre,suf,c at k) -> well_leveled_at k c'`. These need the buffer ops (`green_prefix_concat`/`make_small`/`prefix_concat`) to preserve `buf_all_at_level` — prove those small lemmas (they pair/unpair at adjacent levels; reuse `E.unpair_level`/`E.level_pair`). Then op-level well_leveled preservation by case analysis mirroring the `*_total` proofs.
2. **colors_consistent** half (harder): `green_of_red_k` Case 1/2 outputs are green-headed (`chain_to_kchain_g`, see `kchain_top_color_chain_to_kchain_g_not_red`, `make_small_chain_to_kchain_g_context_ready`); Case 3 outputs `KCons Green (PNode .. Hole ..) (KCons Red ..)` — must show the fresh Red inner is still colours-consistent and the new green head satisfies `tail_green_ready`/`cc_yellow_run`. yellow_wrap_pr turns green->yellow at same depth keeping the tail. Build `green_of_red_k_preserves_colors_consistent` then op-level.
   - WATCH: this is exactly where the prior accretion failed. If after several honest attempts colors_consistent isn't preserved, the `tail_green_ready` clause may be slightly wrong (too strong/weak) — adjust the ONE definition in place, re-check `*_total` still build (they only use it via helpers), and record findings here. Do NOT spawn candidate predicates.
3. If colours preservation stalls: ensure all green+committed, then switch to mission item 2 (RBR/Succ.v) so the night stays productive.

## REMAINING: preservation (the hard residue)
`*_preserves_I_kt : I_kt c -> op = result -> I_kt c'`. Split each into:
- regular_kt_top c': REUSE existing `push/inject/pop/eject_kt4_preserves_regular_top` (proven).
- colors_consistent c' /\ well_leveled c': NEW. This is the genuine work — must survive yellow_wrap_pr (green->yellow same depth, keeps tail) and green_of_red_k repair (Case 1/2 -> green head; Case 3 -> green head over fresh red inner; check tail_green_ready + cc_yellow_run + levels preserved). Look first for existing level-preservation lemmas (grep `chain_levels`/`packet_levels` preserved by green_of_red_k / yellow_wrap_pr / push_kt4). well_leveled may reuse them; colors_consistent is bespoke.

## NEXT STEPS (precise)
1. Reprove `push_kt4_total : forall A x c, I_kt c -> E.level A x = 0 -> exists c', push_kt4 x c = PushOk c'` directly:
   destruct c; KEnding => eexists/reflexivity; KCons _ Hole => `cbn in Hcc; contradiction`; Green => `destruct pre`, B2/B3 use `yellow_wrap_pr_total` + `yellow_wrap_pr_total_pre_of_consistent` (on tail at depth 1), others contradiction via green-shape; Yellow => B1/B2/B3 direct `eexists;reflexivity`, B4 use `yellow_push_red_repair_witness_from_ready` with `Hx`, `packet_levels` (proj1 of `well_leveled_at` of the link) and `ready_at_of_consistent`; Red top => `regular_kt_top` gives `top<>Red` contradiction. Use `cbn -[yellow_wrap_pr green_of_red_k]` when reducing the goal so those stay folded.
2. Symmetric `inject_kt4_total` (suffix side; `yellow_inject_red_repair_witness_from_ready`).
3. `pop_kt4_total` / `eject_kt4_total` directly (no x). pop on Yellow pre=B1 => `green_of_red_k (KCons Red (PNode B0 i suf) tail)` via `yellow_pop_red_repair_witness_from_ready` (no level hyp needed); B0 buffers => packet_levels trivially. Check pop_kt4 def (OpsKT.v:1539+) for exact shapes.
4. Delete `I_kt_implies_kt4_total_state`; update `deque_wc_o1_push`/`deque_wc_o1_inject` to take `E.level A x = 0` and pass it to `*_total`. Build green, commit. Admits then 4 (the `*_preserves_I_kt`).
5. Then attack `*_preserves_I_kt`: regular part via existing `*_preserves_regular_top`; colors_consistent + well_leveled preservation is the remaining hard work (the repair cases). This is the real residue.

## References
- Plan: `kb/runbooks/rebuild-plan-2026-06-02.md`
- Deque invariant spec: `kb/spec/deque-reachable-invariant.md`
- KT99 transcriptions: `kb/spec/section3-recursive-slowdown.md`, `section4-representation.md`, `section6-catenable-deques.md`
- Honest audit: `kb/reports/honest-audit-2026-06-02.md`
