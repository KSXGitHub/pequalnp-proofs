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
