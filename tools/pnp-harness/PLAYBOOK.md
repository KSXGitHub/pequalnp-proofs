# Worker playbook: proving one step for pequalnp.com

You prove ONE Lean 4 step. You do no git, no pull request, no desk call. The orchestrator
does all of that. Your whole job: make `lean` accept a proof of the posted statement, in the
one named file, under the format rules below. Then report.

## The three commands you need

    P=/tmp/claude-0/-home-user-pequalnp-proofs/731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/pnp
    $P/show.py  <STEP>                       # statement, context, sketch, what already failed
    $P/check.sh lean/PEqualNP/Outside/<F>    # type-check your file (seconds, not minutes)
    $P/lint.py  <STEP>                       # format rules + the exact-statement check

`check.sh` runs `lean` directly, so it does not fight other workers for lake's build lock.
At most two checks run at once; yours may wait a moment. Never run `lake build`, never run
`lake update`, never run `lake exe cache get`. Mathlib is already built and pinned.

Run from `/home/user/pequalnp-proofs` and pass the path as `lean/PEqualNP/Outside/<file>.lean`.

## Rules the checker enforces (a break here is an outright refusal)

1. Prove EXACTLY the posted statement. Not stronger, not weaker, not reworded. The file must
   contain, character for character, `theorem <MODULE> : <the posted statement> :=`.
   Do not reformat it, rewrap it, rename a binder, or add parentheses. `lint.py` checks this.
2. No `sorry`. No new `axiom`. No `native_decide`. (`decide` is fine; see the note below.)
3. One theorem, named after the module, at the top level, LAST in the file.
4. Every helper lemma and definition goes inside ONE namespace block named after the module:
   `namespace PEqualNP.Outside.L_x` ... `end PEqualNP.Outside.L_x` (or `..._aux`). Outside that
   block stand only the imports, `open` lines, the four allowed `set_option`s, comments, and
   the one theorem. `namespace`/`section`/`end` start at column 0 and each `end` names what it closes.
5. Imports: only `Mathlib` (or `Mathlib.X`) and the project modules `show.py` lists under IMPORTS.
   After the import lines the word `import` may not appear anywhere, comments included.
6. NO DOUBLE QUOTES anywhere in the file. No string literals.
7. Nothing that runs code at compile time: no `#eval` or any other `#` command, no `initialize`,
   `macro`, `syntax`, `notation`, `elab`, no `attribute` command. These words are refused even
   inside a comment, so reword them if you must mention one.
8. Comments: start every comment line with two hyphens. No `#` headings.
9. Options: only `maxRecDepth`, `maxHeartbeats`, `synthInstance.maxSize`,
   `synthInstance.maxHeartbeats`, each as its own line `set_option <name> <number> in` directly
   above the declaration it serves. The only attributes are `@[simp]` and `@[local simp]`.
10. Prefer Mathlib's types. Declaring your own `structure`/`inductive`/`instance` is allowed but
    then a person must read the pull request before it merges, which is slow. Avoid if you can.

## Limits that matter

The official check gets 20 minutes of compute and about 6.5 GB of memory. A proof that needs
more ends as a FAULT and helps nobody. So: a `decide` over a space of millions is too slow, and
`native_decide` is banned. If you reach for brute force, make the brute force small, or find the
invariant that replaces it. `Decidable` instances that unfold to huge terms blow `maxRecDepth`.

## How to work (this is the part that wins)

Really look at the statement first. Work the smallest case by hand. Then:
- Try the obvious approach. Then try the strange one.
- If the statement is a concrete finite claim, ask what invariant or potential function makes it
  true, rather than enumerating. A monotone quantity that every allowed step can only move a
  little is usually the whole proof.
- If it is an identity or a rewriting fact, `simp`, `omega`, `decide`, `norm_num`, `ring`,
  `Finset.sum_congr`, `List.ext_getElem` and friends go a long way.
- `exact?`, `apply?` and `simp?` are available and cheap; use them on a stuck goal.
- Read what already failed (`show.py` prints it under ALREADY FAILED) and do not repeat it.
- Read the SKETCH if there is one: your job is then only to make Lean accept that argument.
- A counterexample is as valuable as a proof. If you come to believe the statement is false,
  say so and show the witness.

## THE ATTEMPT FLOOR - this is not optional

You may NOT report `CANNOT` until you have actually run `check.sh` on a file you edited at
least EIGHT times, trying genuinely different approaches. Reading the statement, reading the
definitions and concluding "this is an open problem, it needs a lemma nobody has posted" is NOT
an attempt. It is the single least useful thing you can do here, and a report of that shape
with no check runs behind it will be thrown away and the step handed to someone else.

Judging a statement hard on sight is almost always wrong here, for one specific reason: these
steps are hypotheses of a machine-made cut of a bigger claim, and a cut routinely produces a
piece that LOOKS like the whole headline claim but is in fact degenerate - vacuous, or true
because its hypotheses cannot all hold at once, or an instance small enough to settle directly.
So before anything else, spend your first attempts finding out which of these you have:

1. Is a hypothesis contradictory or unsatisfiable? Then `exact absurd ... ` or `omega` or
   `simp_all` closes it outright. Try `exfalso` and look for the contradiction.
2. Is the conclusion weaker than it looks? Count. A bound like `14 <= x3.length` may follow from
   a hypothesis you already have by `omega`, or from a cardinality fact, with no search at all.
3. Is the quantifier structure giving it to you? `intro` everything and LOOK at the real goal.
   Often the goal after `intro` is far smaller than the printed statement suggests.
4. Try the cheap closers on the real goal, in this order, and record what each says:
   `simp_all`, `omega`, `decide`, `norm_num`, `aesop`, `tauto`, `exact?`, `apply?`.
5. Only then start building the argument by hand.

Always `intro` the binders and print the goal before you decide anything about difficulty.

Stay on it for at least 20 minutes of genuine attempts before you give it back. Do not give up
after one failed tactic. Equally: do not grind past roughly 30-35 failed check runs. At that
point report honestly; an honest "I could not" is useful work here, and a wrong claim is the
only real failure. Your report must state how many check runs you made and name the tactics you
tried, so include that in your NOTE.

## What to report back (last lines of your reply, exactly this shape)

If it builds (`check.sh` printed `CHECK_OK` AND `lint.py` printed `LINT OK`):

    VERDICT: PROVED
    FILE: lean/PEqualNP/Outside/<file>.lean
    NOTE: <one or two sentences on the idea of the proof>

If it does not, pick the reason that fits and report:

    VERDICT: CANNOT
    REASON: hypothesis_too_weak | missing_lemma | statement_seems_false | does_not_elaborate | out_of_time | other
    NOTE: <what you tried, what the real obstacle is, and for statement_seems_false the witness>

Use `does_not_elaborate` only when the posted statement itself will not compile against the
project (for example it names something not published yet) - release that at once, it is their bug.
Use `missing_lemma` when the step is too big and needs smaller steps posted first.

Never edit any file but your own. Never touch git. Never change the statement. If `lint.py`
complains, fix your file, not the statement.
