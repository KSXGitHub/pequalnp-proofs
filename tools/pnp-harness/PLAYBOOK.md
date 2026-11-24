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

## IS THE STEP FALSE? Check this early - it has already paid off once

These steps are hypotheses of machine-made cuts, and a cut can produce a statement that is
simply FALSE. We have already refuted one this way (L-meta-3628) in four check runs. A
counterexample is worth as much as a proof here, so look for it deliberately.

The pattern that broke L-meta-3628, worth testing on any step shaped like it: the conclusion
quantified over EVERY smaller object (every fan-in-two circuit under a gate budget) and asserted
each one computes a given function. A universally quantified conclusion like that is refuted by
the DEGENERATE member of the family - the empty circuit, the zero function, the empty list -
whenever the hypotheses do not rule it out. The empty circuit has gate count zero, so it meets
any budget of one or more, yet it is constant, while the step's own hypothesis said the target
function is non-constant. That is the whole refutation.

So, concretely: if the goal after `intro` is `∀ (smaller thing), <budget> → <it computes f>`,
instantiate it at the degenerate thing and see whether the hypotheses let you. Likewise if the
conclusion is an equality of functions, apply `congrFun` at a well-chosen point and look for a
mismatch.

To test a refutation, write a SCRATCH file (never your step's file) proving the negation:

    P=/tmp/claude-0/-home-user-pequalnp-proofs/731ccd8c-0494-56c8-b77c-6e2443ae238b/scratchpad/pnp
    printf '  intro h\n  have key := h <args...>\n  ...\n' > /tmp/myproof.txt
    $P/mkrefute.py <STEP> /tmp/myproof.txt      # writes a scratch file: ¬ (the posted statement)
    $P/check.sh <the path it prints>

`mkrefute.py` inserts the posted statement verbatim, so a `CHECK_OK` there is a real refutation
of the real statement - not of your paraphrase of it. Do NOT hand-retype the statement into a
restatement of your own and claim a refutation from that; it proves nothing about the posted step.
If it checks, report `statement_seems_false` and give the witness in your NOTE. Leave the scratch
file in place and name its path so the orchestrator can keep it.

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

## THREE THINGS LEARNED THE HARD WAY - read these before you start

### 1. Check whether the PARENT is already proved. This closed a step in three runs.

If `show.py` describes your step as "one case of a split of L-meta-NNNN" or "step k of n of a
checked cut of L-meta-NNNN", then GREP FOR THAT PARENT FIRST:

    grep -l "theorem PEqualNP.Outside.L_meta_NNNN" /home/user/pequalnp-proofs/lean/PEqualNP/Outside/*.lean

L-meta-3935 turned out to be exactly its parent L-meta-3095's statement plus one extra, UNUSED
hypothesis - and the parent was already proved in the repository, 3215 lines, no sorry. The
whole gate-elimination argument the brief described was unnecessary. Because the import list is
restricted, you cannot `import` the parent module; instead copy the parent's file, rename its
namespace to your module, and discharge your goal through its internal final lemma, `intro`-ing
the extra hypotheses and ignoring them.

A split's siblings are all corollaries once the parent is proved. This costs one grep. Do it.

### 2. "No other declarations" is about the ENVIRONMENT, not the source text.

A reduction file containing exactly one `theorem` was REJECTED upstream:

    REJECTED (reduce-extra): ... declares more than its theorem:
    [PEqualNP.TopForm.centreless.congr_simp, ... , PEqualNP.CircuitLowerBounds.Circuit.size.eq_1]
    A reduction file holds the one theorem and nothing else

Those five were AUTO-GENERATED and appear nowhere in the source:
  - `X.eq_1` is an EQUATION lemma, emitted when a tactic unfolds a definition by equation:
    `simp [SomeDef]`, `rw [SomeDef]`, `unfold SomeDef`, `dsimp [SomeDef]`.
  - `X.congr_simp` is a CONGRUENCE lemma, emitted when simp is asked to rewrite with a
    definition.
They land in the namespace of the DEFINITION, not yours, so they also break the rule that only
the one theorem stands outside the module's namespace block in a direct proof.

HOW TO AVOID THEM. Never pass a project DEFINITION to simp / simp only / rw / unfold / dsimp.
Passing ordinary Mathlib LEMMAS to simp is fine - it is unfolding definitions that generates
these. Instead:
  - state a definitional equality with an explicit type and close it by `rfl`, which generates
    nothing:   `have hsz : C.size = C.gates.length := rfl`   then rewrite with `hsz`;
  - use `show` / `change` to re-express a goal definitionally;
  - reach for named Mathlib lemmas (`Finset.card_filter_le`, `Finset.card_le_card`,
    `Finset.card_range`) and prove a subset with an explicit `fun x hx => ...` term.

### 3. Verify with `decls.sh`, not by reading your own file.

    $P/decls.sh lean/PEqualNP/Outside/<your file>.lean

It asks Lean what the file actually adds to the environment. For an `R_` reduction, SUCCESS is
exactly ONE name. For an `L_` proof, every added name should sit inside
`PEqualNP.Outside.<module>`; anything in another namespace is a risk.

RUN ALL THREE GATES before claiming anything: `lint.py` (format and exact statement),
`check.sh` (Lean accepts it, no sorry), `decls.sh` (nothing extra in the environment). `LINT OK`
alone means only that our own rules passed - it is not the upstream checker, and it missed the
rejection above.
