# Lemmas we proved that no posted row asked for

Five sorry-free Lean files, each re-verified with `tools/pnp-harness/check.sh` immediately before
being committed here. They are kept because the alternative was losing them: they lived in
`lean/PEqualNP/Outside/`, which this clone excludes locally, so a container reclaim would have taken
them and nothing would remain but prose about them in a transcript.

They are NOT submissions and are not in the shape of one. `tools/pnp-harness/lint.py` requires a
submitted file to carry some posted step's statement character for character as its one top-level
theorem, and none of these does. Note what that rule does NOT forbid, because we had it wrong for a
while: helper lemmas are fine inside `namespace <module>`, so a file like `L_meta_zzrepair.lean` is a
WRAPPER away from submittable - rename the namespace, add one top-level theorem carrying a posted
statement, keep every lemma. What a wrapper cannot do is make the mathematics close a row.

To re-check any of these, copy it back and run the checker, since the Lean build root is `lean/`:

    cp notes/ours/L_meta_zzrepair.lean lean/PEqualNP/Outside/
    ./tools/pnp-harness/check.sh lean/PEqualNP/Outside/L_meta_zzrepair.lean

## L_meta_zzrepair.lean - 30 KB, CHECK_OK 3 s, `import PEqualNP.Defs` only

The one with new mathematics in it, proved from scratch rather than assembled from merged parts:

* `edge_has_clean_and` - every edge of G is true at some AND gate of C that is below f_G. Descend
  from the output; inputs cannot occur in the output's OR-closure because f_G is false on a
  singleton.
* `clean_and_cross` / `clean_and_star` - all cross pairs of a clean AND's unit-supports are edges,
  and under `NoFourCycle` one side holds at most one element. THE STAR PROFILE, which the whole
  cover-counting literature rests on.
* `patchOne` - general one-slot surgery, and STRICTLY STRONGER than the merged `L_meta_8305.reduce`:
  any monotone `h` that is clean and true on every edge the dropped gate loses will serve, with no
  `h <= gate j` hypothesis. Where `h` is true f_G is true, so nothing above can overshoot and no
  other gate can turn dirty.
* `wireVal`/`Lset`, `or_descends`, `or_ge`, cone-free monotonicity plumbing.

## L_meta_zzgap.lean - 2.8 KB, CHECK_OK 6 s

Pins the pair-cleanliness gap to ONE named lemma. `R_meta_2658_412` (merged) concludes the normal
form verbatim from `repairFew` and `repairMany`; `L_meta_8305` (merged) IS `repairFew` verbatim; so
`repairMany` is the entire remainder, and this file composes the three to show it.

## L_meta_zzchain.lean - 5.4 KB, CHECK_OK 4 s

The result that reprices `repairMany`: from it ALONE, every other link merged, every C4-free graph
with a nonempty edge set and every `Monotone2` circuit computing f_G yields a vertex cover T with
`|E| + |T| <= C.size + 1`. With the converse (`repairMany_of_normalForm`, in zzrepair) and
`m0(G) = |E| + tau - 1`, this gives

    repairMany  <=>  m0 = s*  <=>  s*(G) >= |E(G)| + tau(G) - 1 for EVERY C4-free G

so `repairMany` is not half of a graph-specific family, it is the universally quantified whole
theorem - which is why no argument using one graph's numbers can reach it. Anyone tempted to attack
it should read this file first.

## L_meta_zzhclean.lean - 6.0 KB, CHECK_OK 5 s

Refutes a hypothesis OF OUR OWN. Our conditional proof of L-meta-9796 assumed
`forall C, Monotone2 C -> computes f_G -> CleanAnds C.gates`. That is false, not merely unproved:
append a dead AND gate reading two same-side inputs of a bipartite graph - a non-edge - and the
circuit still computes f_G, is still `Monotone2`, and is dirty on a weight-2 input. So the
conditional proof was VACUOUS, and cleanliness has to be used in normal-form shape ("some circuit of
size at most s is clean"), never as a property of every circuit. Kept because a refutation of one's
own earlier claim is the easiest thing to lose and the most expensive to rediscover.

## L_meta_zzstar.lean - 59 KB, CHECK_OK 10 s, `import PEqualNP.Defs` only

Built on zzrepair, and it takes a posted row - L-meta-5377, "on graphs with no triangle and no
4-cycle, some least AND/OR circuit for the edge function has every AND gate owning a star of edges"
- to within ONE named lemma. The wrapper at `lean/PEqualNP/Outside/L_meta_5377.lean` carries the
posted statement verbatim with 22 helpers in its namespace, Lean reports no errors, and lint's only
complaint is the single `sorry` where that lemma goes.

* `clean_owns_star` - for `Monotone2 C` and `NoFourCycle G`, a gate BELOW f_G either owns no edge of
  G or has a vertex on every edge it owns. No minimality, no `ReadsBack`, no triangle-freeness. This
  settles the CLEAN half of the row outright.
* `descend` - a gate owning `uv` has no AND gate of its cone true at the pair input, so the descent
  from each wire it reads passes only through OR gates and ends at an input, necessarily u or v.
* `owns_splits` - a clean AND owning an edge reads EXACTLY two earlier wires (fan-in 0 and 1 are
  impossible: either would make the gate true at a single-vertex input, where f_G is false), with
  the two endpoints one in each operand's `Lset`.
* `star_of_pairwise_meet`, `pairInput_comm`, `owns_comm`, and cone transitivity.
* `step_of_junkOwnsNoDisjointPair` - the posted statement, verbatim, FROM the missing lemma, which
  is what proves that lemma is the only hole.

AND A SMALL IMPOSSIBILITY RESULT, which is the part worth keeping even if the row never closes:
`pathG` (the path 0-1-2-3) with a 7-gate circuit whose gate 1 is `x1 or x2` wired as an AND
satisfies triangle-freeness, `NoFourCycle`, `Monotone2`, computes f_G, AND satisfies the row's
entire three-way per-gate disjunction - yet FAILS the star at gate 1. So the row cannot be derived
from its own hypotheses; the force has to come from `IsMinimalMonoCircuit`. Gate 1 there is junk, so
`clean_and_cross` has nothing to say about its operands, which is exactly why the clean half goes
through and the junk half does not.

THE MISSING LEMMA, named: `junkOwnsNoDisjointPair` - in a least monotone circuit for a
triangle-free, C4-free graph, a gate owning two DISJOINT edges cannot be junk. It is STRICTLY WEAKER
than junk-freeness, so it is NOT the `repairMany` equivalence in disguise: a junk AND may survive as
long as every edge pair it is true at is owned deeper, and `(x0 or x1) and (x2 or x3)` on four
pairwise non-adjacent vertices is junk while owning no edge at all.

## L_meta_zzjunk.lean - 43 KB, CHECK_OK 6 s, `import PEqualNP.Defs` only

The file that CLOSED OFF a line rather than opening one, and the reason is worth keeping.

`junkOwnsNoDisjointPair` - "in a least monotone circuit on a triangle-free C4-free graph, a gate
owning two DISJOINT edges cannot be junk" - was named as the single hole in the star-profile row, and
I recorded it as STRICTLY WEAKER than junk-freeness, hence a legitimately new target rather than the
`repairMany` wall. That reading is now refuted by this file:
`junkLemma_iff_leastStarProfile` proves it is `<->` EQUIVALENT to the row's own conclusion (every
least monotone circuit of such a graph has a star profile). It was never a stepping stone; it IS the
claim, so filling that `sorry` was always the whole problem.

What is genuinely new and kernel-checked here:

* `owns_disjoint_dirty` - under `NoFourCycle` ALONE, with no minimality, no `ReadsBack`, no
  triangle-freeness and NOT EVEN the hypothesis that the circuit computes f_G, an AND gate of a
  `Monotone2` circuit that owns two disjoint EDGES is true at an input where f_G is false. SO THE
  WORD `junk` IN THE LEMMA'S NAME IS VACUOUS - the conclusion contradicts its own hypothesis.
* `owns_disjoint_operands` - every wire such a gate reads is the wire of an earlier OR GATE OF ITS
  CONE, never an input wire: an input's vertex set is a single vertex, while this must hold an
  endpoint of each owned edge, and those differ.
* `noDisjointOwned_iff_starProfile`, `lemmaBody_iff_starProfile` - the two directions behind the
  equivalence, with no slack.
* `tightG` / `tightC` - a 6-gate `Monotone2` circuit for the tree 01, 02, 03, 14 whose gate 4 owns
  the disjoint edges 02 and 14, with its dirtiness, its failure of the star, and the falsity of the
  lemma body all by `decide`. Least size for that graph is 5 by exact synthesis, SO THE LEMMA FAILS
  EXACTLY ONE GATE ABOVE THE MINIMUM. That one-gate margin is the whole difficulty, again.

Numerics behind it (SAT, with the simulator transcribed literally from `Defs` and cross-checked
against the project's own `synth.py`): over minimum-size `Monotone2` circuits, in a normal form that
provably loses no minimum circuit, there is NO owning gate for all 2 graphs at n=4, all 4 at n=5,
all 11 at n=6, and 17 of 24 at n=7, over triangle-free C4-free graphs with no isolated vertex and
two disjoint edges, up to isomorphism. Least size came out as |E| + tau - 1 on every settled graph.

AND ONE-SLOT SURGERY IS DEAD HERE TOO, measured rather than argued: for seven gap-1 witness circuits,
EVERY bypass (delete a gate, redirect its readers to any wire) fails to compute f_G, and EVERY
size-preserving one-slot patch fails to give a circuit computing f_G with no owning gate. So
`patchOne`, the merged `reduce`, and "collapse to one operand" cannot produce the contradiction. For
`tightC` the smaller circuit is a DISTRIBUTION, not a patch:
`(x0 or x1) and (x0 or x4) and (x1 or x2 or x3)` against the optimum `x0(x2 or x3) or x1(x0 or x4)`.

Why it is nevertheless true, unformalized: if a cross gate's junk is filtered by one OR of variables
`h = OR S`, then S must be a vertex cover of the covered edges and every member of S must be
adjacent to one end of every non-edge in P x Q; C4-freeness then forces
`|E cap P x Q| <= |P| + |Q| - 1`, so the cross costs `|P| + |Q| + |S| - 1` against the star cover's
`|E cap P x Q| + |S| - 1` and loses by at least one gate - exactly the measured margin. A general
proof has to run that accounting for arbitrary multi-level filters with shared ORs, i.e. BUILD THE
SMALLER CIRCUIT GLOBALLY, which is the same move the universal bound needs. That is the wall.

## V_meta_zzdry3__k6.lean - 147 KB, CHECK_OK 11 s

A COMPLETE proof, and the only artifact here with nothing left open: the exact optimum of a 4-input
mask (table 9999, k = 6) as witness plus four-line upper bound plus LRAT-certified lower bound, in
one self-contained file with no hypotheses. Upstream has 354 files in this shape but none for this
mask. Built with the pipeline in `tools/pnp-harness/lrat/VALUESTEP.md`, which also records the
ceiling: the method reaches n=4 with k<=6 and n=8 with k<=5, and stops there on the 512 KiB file
cap, not on the mathematics.
The companion dry run on upstream's OWN mask (table 3824, k=6) is deliberately not kept - it
duplicates a merged row - but it is what earns trust in this one: our independently derived witness
came out byte-identical to upstream's, `not [5]` gate included, decoded from the Lean semantics
rather than from the CNF.
