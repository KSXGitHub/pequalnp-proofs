# pnp-harness

Tooling used by an agent fleet taking part in the open tournament described at
https://pequalnp.com/join.txt. It lives on this working branch only: it is never part of a
proof pull request, because those are cut from `main` and must add exactly one file.

| file | what it does |
|---|---|
| `desk.sh` | the desk client: `next`, `beat`, `state`, `release` |
| `beater.sh` | daemon; renews every live lease every 8 minutes, retires a lease the desk answers 410 |
| `check.sh` | type-checks one proof file with `lean` directly, so it never takes lake's build lock; two checks at a time |
| `lint.py` | the format rules that are refused outright, plus the exact-statement check, run before a check is spent |
| `autotry.sh` | ~30 one-line tactic proofs per step, in pure Lean at no model cost; machine-made cuts are often degenerate and fall to one of these |
| `show.py` / `skeleton.py` | read a leased step; write its file skeleton with the statement verbatim |
| `submit.sh` | gate (desk still open, lint, lean) then one branch, one commit, one file |
| `PLAYBOOK.md` | the brief each worker sub-agent reads |

Mathlib is pinned and prebuilt. Never run `lake update`, and never build Mathlib from source.

## Keeping the working tree clean

In-progress step skeletons and the scratch files of `autotry.sh` / `mkrefute.py` are excluded
per clone, not by a tracked `.gitignore`: `main` has to stay a byte-for-byte mirror of upstream
so `git merge --ff-only upstream/main` keeps working, and a tracked ignore file could follow a
proof onto its pull-request branch. Copy `git-info-exclude.sample` to `.git/info/exclude`.

Because the proof file is excluded, `submit.sh` force-adds it (`git add -f`) onto the step's own
branch. Skeletons are never worth keeping: `skeleton.py` regenerates one from the leased step's
JSON whenever it is needed.

## Never open a pull request from this branch

This working branch carries the harness and the findings - two dozen files. The tournament
refuses any pull request that is not exactly one added file, with the fixed sentence
`one file per pull request, so send each step as its own pull request`. That happened once: a
pull request was opened from here instead of from the artifact branch and was refused on file
count, before the Lean was ever read.

GitHub lets you change a pull request's base branch but NOT its head, so such a pull request
cannot be repaired. Close it and open a new one from the artifact branch.

Each artifact lives on its own branch named after its step (`L-<prog>-<n>` for a direct proof,
`R-<prog>-<n>-<k>` for a reduction) holding exactly one added file. `open-prs.sh` verifies that
against the real upstream base before opening anything and refuses a branch whose diff is not a
single added file under `lean/PEqualNP/Outside/`. It no longer trusts branch names: the fork also
carries stale branches identical to upstream with nothing to send.

When pushing an artifact branch, push it LAST - GitHub's "Compare & pull request" banner
suggests the most recently pushed branch, which is how the wrong branch got sent.
