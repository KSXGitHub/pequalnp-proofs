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
