# Pull requests ready to open, blocked on session GitHub scope

This session CANNOT open a pull request against `open-goat/pequalnp-proofs`. GitHub access is
scoped to `ksxgithub/pequalnp-proofs`, and `add_repo open-goat/pequalnp-proofs` is refused because
this environment checks every repository out at `<cwd>/<name>` - two repositories with the same
name cannot share one session. That is a checkout-layout limit, not a permissions problem, so
retrying does not help; `gh pr create` and `gh api .../pulls` both return 403. The earlier six
pull requests went out before the fork was attached under that name.

Each artifact below is fully gated (lint, check, decls) and already PUSHED as its own branch to
our fork, cut from `upstream/main` and containing exactly one file. Opening the pull request is one
click per row.

## 1. L-meta-11461 - READY

* branch `L-meta-11461` at `e51277b0`, one file `lean/PEqualNP/Outside/R_meta_11461_1.lean`
* gates: `LINT OK`, `CHECK_OK` (9 s), `DECLS_OK`; `eligible.py` said slots 0/3 at submit time
* body to paste: `pr11461.md` in this directory
* open it here:
  https://github.com/open-goat/pequalnp-proofs/compare/main...KSXGitHub:pequalnp-proofs:L-meta-11461?expand=1

Content: the step's clause (e), the double re-read condition, is DERIVED rather than assumed. The
only hypothesis is that some circuit meeting clauses (a)-(d) has an AND gate as its output wire
whose two operands each read false on the one-point and the one-line input - three facts about one
gate plus two evaluations, all decidable, in place of a quantification over 3-valued labellings of
every wire for both Booleans. Consistent: dropping only the size bound gives a 55-gate witness (two
disjoint copies of any Fano circuit, ANDed).

## Not submittable: R_meta_4079_409 - LOST THE RACE

Kept at `tools/pnp-harness/done/R_meta_4079_409.lean` and worth reading, but it CANNOT be
submitted: L-meta-4079 was drawn with reduction slots 0 of 3 and a fresh draw twenty-eight minutes
later reported 3 of 3. Competitors filled every slot while the work was in progress, and submit.py
aborted on its own hard gate - correctly, since #12891 and #12936 were closed unchecked for exactly
this. The lease was released honestly as `missing_lemma`.

Its new content, should a slot ever free: `purity` - if an AND gate lies strictly inside the cone of
another AND gate then it is junk, because top form forbids an AND below f_G inside an AND's cone.
With `|junk| = 2` that pins the cone order of every AND gate and leaves two cases, and it discharges
`|U*| = 3` outright. None of the six merged 4079 reductions uses it.

## Lesson recorded in the tooling

`eligible.py` reads the slot count from the step JSON saved when the step was leased, and nothing in
the harness can refresh it - `desk.sh state` returns only state, holders and since. So the count
goes stale and "re-run eligible.py before you finish" was useless advice: the agent did re-run it
and was told OPEN by the same stale file. It now prints the age of the snapshot and says that only
another draw (`desk.sh next --proof-of <id>`) refreshes it.
