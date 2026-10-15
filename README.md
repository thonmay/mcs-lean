# Dynamic MCS Ordering Maintenance

A machine-checked (Lean 4 / Mathlib) study of how a **Maximum Cardinality
Search (MCS)** vertex ordering behaves under edge updates: a stability theorem
with certified obstructions, the exact locality of a single-edge update, a
verified executable probe-then-repair implementation, and a unit-cost count
along its real control flow.

**Authors:** Md Thoriqul Islam Thonmay, Gregory Morse (ELTE).
**License:** Apache-2.0.

**Accompanying preprint:** *How rigid is maximum cardinality search? Stability
and locality of MCS orderings under edge updates, verified in Lean* (in
preparation). The preprint pins this repository to the annotated tag
[`mcs-arxiv-v4`](https://github.com/thonmay/thesis-lean/releases/tag/mcs-arxiv-v4)
(commit `c4c2c0f`).

**Registered formalization:** Palomar Registry entry
[`PALOMAR-2026-10-04-000009`](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-04-000009&version=2),
version 2, status `registered`, built from commit `c4c2c0f`
(machine-readable record:
[`PALOMAR-2026-10-04-000009-v2.json`](https://data.palomar-registry.org/entries/PALOMAR-2026-10-04-000009-v2.json)).
Review outcome `neutral` with no review warnings; trust level `high`. Version 1
was registered from the ancestor commit `a872fdd` (37 of the current 41
comparator theorems). Registration is a preservation and indexing service, not
a review endorsement.

---

## What is MCS?

Maximum Cardinality Search is a graph traversal introduced by Tarjan and
Yannakakis (1984). It numbers vertices from 1 to *n* by repeatedly selecting
the unnumbered vertex with the most already-numbered neighbours. This
formalization breaks ties by lowest index (the *canonical* ordering) for the
update results, and allows any legal tie-break for the stability results. On a
chordal graph, the reverse of any MCS ordering is a perfect elimination
ordering, which gives a linear-time chordality test. MCS is a simpler variant
of the lexicographic breadth-first search (LexBFS) of Rose, Tarjan and Lueker
(1976), with the same `O(n + m)` running time. The two searches produce
incomparable families of orderings: neither contains the other, on general
graphs (e.g. `K₂,₃`) and even on chordal graphs (e.g. a 5-clique plus a vertex
joined to one clique vertex and another joined to two).

The question studied here is *how rigid* an MCS ordering is: when do two graphs
share an MCS ordering, and how much of a given ordering must change after a
single edge is inserted or deleted?

## Results

All results below are proved in Lean for every graph size `n`, except the
probe bound marked *paper-level*.

- **Stability theorem.** If, along every **proper common MCS prefix**, the
  neighbour counts in `G'` exceed those in `G` by zero or one, the two graphs
  share an MCS ordering (`exists_common_ordering_prefix`). This is strictly
  weaker than requiring the bound on every subset; the every-subset version
  `exists_common_ordering` is retained as a special case. In particular,
  inserting or deleting a *matching*, or flipping a single edge, always
  preserves a common MCS ordering.
- **Online form.** Under the same prefix-only hypothesis, any common MCS prefix
  extends to a full common ordering (`common_order_extends_prefix`): a
  maintainer that picks a common-maximum vertex at each step never needs to
  look ahead or backtrack.
- **Certified obstructions.** Neither part of the hypothesis can simply be
  dropped. Inserting a triangle (`n = 5`), a `P_4` (`n = 6`) or a `2P_3`
  (`n = 8`) shows the `+1` bound cannot be relaxed to `+2`, and a *disjoint*
  mixed update (one insertion and one deletion, `n = 4`) shows the
  one-directional (insert-only or delete-only) condition is needed. Each
  destroys every common ordering, certified by kernel `decide` on explicit
  instances. The triangle and the `P_4` show the same inflation phenomenon on
  structurally different insertions: the triangle is a clique, while the `P_4`
  is triangle-free. The hypothesis is sufficient, not necessary: inserting a
  2-edge path inflates one vertex by two yet leaves a common ordering on every
  host graph (exhaustively checked up to `n = 6` with
  `scripts/mcs_stability.py`).
- **Correctness.** The probe-then-repair update scans for the first step whose
  old choice is no longer a legal MCS pick and re-greedily rebuilds the suffix
  from there. Every order it produces is the canonical MCS ordering of the
  updated graph, which is unique, so the update equals from-scratch
  recomputation.
- **Locality.** An insertion can first change the canonical ordering only at a
  position strictly between the two endpoints: positions up to the earlier
  endpoint and after the later endpoint stay legal, and the later endpoint's
  own position never breaks (`no_break_at_laterPos`). Inside that open window
  the break criterion is decidable from the *old* graph's counts
  (`insert_break_iff_old`). A deletion can first change the ordering only at
  the later endpoint's position. When no break fires, the ordering is
  literally unchanged.
- **Verified executable.** A boolean-adjacency implementation
  (`execInsertUpdate` / `execDeleteUpdate`) is proved to refine the abstract
  update.
- **Unit cost.** Instrumented versions count legality checks and pick steps
  along the real control flow; their first projection is provably the plain
  update. A deletion whose probe finds no break costs **exactly 1** unit
  (`exec_delete_cost_of_no_break`). An insertion whose probe finds no break
  costs at most `laterPos - earlierPos` units (`exec_insert_cost_of_no_break`);
  this count includes the later endpoint's position, which the executable probe
  checks even though it never breaks. The worst case is at most `n` units for an
  insertion and `n + 1` for a deletion, which **matches static recomputation**:
  no asymptotic speedup over recomputing from scratch is claimed. One unit is a
  single legality check or pick step, and each unit is itself superconstant
  work in this naive implementation (`pickAt` filters the chosen list per
  candidate), so the model compares the update with recomputation *within the
  same model* and says nothing about wall-clock parity with the linear-time
  static algorithm of Tarjan and Yannakakis.
- **Sublinear first-break probe (paper-level).** The insertion probe is
  answerable in `O((deg(v)+1) log n)` time, independent of the window length,
  via per-value position lists and range-max structures. This bound is proved
  on paper, not in Lean; its combinatorial core (the count `c_v(j)` is a step
  function with at most `deg(v)+1` plateaus) is machine-checked
  (`neigh_take_image_card_le`, `neigh_take_sub_eq_count`). The worst-case full
  update is still `O(n+m)`; the gain is certifying a no-change update in `o(n)`
  for `deg(v) = o(n/log n)`.

## Theorem map

The Palomar comparator contract is the 41-name list in
[`comparator.json`](comparator.json). Each name is a real theorem in
[`Solution.lean`](Solution.lean) with a matching `sorry` statement in
[`Challenge.lean`](Challenge.lean). Both files are generated from a single
source of truth ([`scripts/gen_comparator_wrappers.py`](scripts/gen_comparator_wrappers.py))
so the posed and proved types stay textually identical.

| Category | Theorems |
|---|---|
| Correctness | `init_valid`, `insert_update_valid`, `delete_update_valid`, `greedySuffix_full`, `update_from_prefix` |
| Uniqueness / update = recompute | `IsMCSOrdering_unique`, `insert_update_eq_initOrder`, `delete_update_eq_initOrder` |
| Locality | `legal_upto_earlierPos`, `legal_after_laterPos`, `delete_legal_between`, `insert_break_iff`, `no_break_at_laterPos`, `insert_break_iff_old`, `insert_update_eq_self_iff`, `delete_update_eq_self_iff` |
| Executable refinement | `exec_insert_update_eq`, `exec_delete_update_eq` |
| Unit cost | `exec_insert_cost_le`, `exec_delete_cost_le`, `exec_insert_cost_of_no_break`, `exec_delete_cost_of_no_break`, `exec_insert_cost_of_break`, `exec_delete_cost_of_break`, `exec_insert_update_c_fst`, `exec_delete_update_c_fst` |
| Executable bridge | `setEdge_preserves_symm`, `setEdge_preserves_loopless`, `mcsOrder_eq_greedySuffix`, `exec_insert_recompute_valid`, `exec_delete_recompute_valid` |
| Stability | `exists_common_ordering`, `exists_common_ordering_prefix`, `common_order_extends_prefix`, `insert_matching_common_order`, `delete_matching_common_order`, `flip_common_order` |
| Stability obstructions | `triangle_no_common_order`, `p4_no_common_order`, `mixed_matching_no_common_order`, `two_p3_no_common_order` |

All 41 theorems audit to only the three standard Lean axioms:
`propext`, `Quot.sound`, `Classical.choice` (no `sorry`, no `native_decide`).
`mcsOrder_eq_greedySuffix` and the two `*_recompute_valid` theorems certify
recomputation rather than the update; they are kept for the executable bridge.

## Repository layout

```
Challenge.lean            Posed statements (sorry bodies) + canonical definitions
Solution.lean             Proved versions of every comparator theorem
AxiomAudit.lean           #print axioms for each comparator theorem
ThesisLean/
  Basic.lean              Module header and shared imports
  ChallengeDefs.lean      Canonical definitions (byte-identical to Challenge.lean DEFS block)
  Correctness.lean        Uniqueness, locality, update = recompute
  ExecUpdate.lean         Executable updates, refinement proofs, unit-cost model
  Stability.lean          Common-ordering theorem, online form, matching corollaries, obstructions
  Exec.lean, ExecFlip.lean, ExecBridge.lean, McsInvariant.lean,
  CardBridge.lean, BridgeSteps.lean, BridgeParts{A,B,C}.lean,
  BridgeAssembly.lean, SolutionBridge.lean
                          Executable layer and transport lemmas to the abstract model
  Formal_gen001c01_*.lean, Formal_gen003c01_*.lean
                          Core DynamicMCS development (graph searches, updates, validity)
scripts/
  check_challenge_defs.sh     Verify Challenge.lean DEFS block matches ChallengeDefs.lean
  sync_challenge_defs.py      Copy the DEFS block from ChallengeDefs.lean into Challenge.lean
  check_axioms.sh             Axiom audit for all comparator theorems
  gen_comparator_wrappers.py  Single-source generator for comparator blocks
  mcs_stability.py            Exhaustive stability harness (cross-check for counterexamples)
  stab.c                      Independent C brute-force stability checker (referee-written)
  mcs_highn_crosscheck.py     High-n cross-check of the adopted candidate vs from-scratch MCS
  incomparability_witness.py  MCS/LexBFS ordering-family incomparability (204/204/40)
  candidates/gen003_c02.py    The adopted dynamic-MCS candidate the cross-check runs
docs/
  LITERATURE.md               Literature and provenance notes
  ROADMAP-*.md                Historical roadmap of the Palomar and arXiv revisions
```

The empirical scripts back the paper's claims: `mcs_stability.py` (exhaustive
small-`n` enumeration of the certified obstructions), `incomparability_witness.py`
(the 204/204/40 MCS-vs-LexBFS witness) and `mcs_highn_crosscheck.py`, which runs
the adopted Python candidate on random graphs up to `n = 200` and checks that,
after every edge flip, its ordering is a legal MCS ordering and equals a
from-scratch recomputation. That last check empirically links the Lean
*encoding* to the Python candidate; it is not a proof.

## Build and verify

Requires Lean `v4.35.0-rc2` (see [`lean-toolchain`](lean-toolchain)) and Mathlib.

```bash
lake exe cache get && lake build          # build everything (8975 jobs)
bash scripts/check_challenge_defs.sh      # Challenge.lean defs match ChallengeDefs.lean
bash scripts/check_axioms.sh              # all theorems use only propext/Quot.sound/Classical.choice
```

The CI workflow (`.github/workflows/lean_action_ci.yml`) runs the build, both
checks above, and an independent kernel re-validation of every module with
[leanchecker](https://github.com/digama0/lean4lean). The
`palomar-preflight.yml` workflow runs Palomar's own reusable verification
pipeline on a chosen commit.

The stability obstructions are cross-checked against
[`scripts/mcs_stability.py`](scripts/mcs_stability.py), an independent Python
harness that exhaustively enumerates all MCS orderings on small instances:

```bash
python3 scripts/mcs_stability.py --n 5 --pattern K3  --mode ins
python3 scripts/mcs_stability.py --n 6 --pattern P4  --mode ins
python3 scripts/mcs_stability.py --n 4 --pattern 2K2 --mode mixed
python3 scripts/mcs_stability.py --n 6 --pattern P3  --mode ins   # sufficiency-not-necessity: 0 disjoint
```

The MCS/LexBFS ordering-family incomparability (204/204/40) and the high-`n`
candidate cross-check are reproduced by:

```bash
python3 scripts/incomparability_witness.py                 # asserts 204/204/40
python3 scripts/mcs_highn_crosscheck.py --nmax 200         # candidate vs from-scratch MCS
```

## Provenance

| Reference | Contribution |
|---|---|
| D. J. Rose, R. E. Tarjan, G. S. Lueker. *Algorithmic Aspects of Vertex Elimination on Graphs.* SIAM J. Comput. 5(2):266-283, 1976. [doi:10.1137/0205021](https://doi.org/10.1137/0205021) | Introduced LexBFS and linear-time chordal graph recognition via lexicographic search. |
| R. E. Tarjan, M. Yannakakis. *Simple Linear-Time Algorithms to Test Chordality of Graphs, Test Acyclicity of Hypergraphs, and Selectively Reduce Acyclic Hypergraphs.* SIAM J. Comput. 13(3):566-579, 1984. [doi:10.1137/0213035](https://doi.org/10.1137/0213035) | Introduced Maximum Cardinality Search (MCS) as a simplified alternative to LexBFS. |
| J. Holm, K. de Lichtenberg, M. Thorup. *Poly-logarithmic Deterministic Fully-Dynamic Algorithms for Connectivity, Minimum Spanning Tree, 2-Edge, and Biconnectivity.* J. ACM 48(4):723-760, 2001. [doi:10.1145/502090.502095](https://doi.org/10.1145/502090.502095) | Foundational fully-dynamic graph algorithm techniques (context for the dynamic setting). |

The re-greedy in this formalization is a naive greedy recomputation, not a
bucket implementation. We found no prior formalization of MCS or of dynamic MCS
ordering maintenance in the proof-assistant libraries we surveyed; this is a
negative claim limited by that survey (see [`docs/LITERATURE.md`](docs/LITERATURE.md)).
See [`formalization.yaml`](formalization.yaml) for the full provenance,
cost-model fidelity notes, and AI-assistance disclosure.
