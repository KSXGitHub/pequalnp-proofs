# Verified artifacts pushed to the fork

A row marked SUBMITTED already has its pull request. The rest still need one.

Why they are waiting: the Claude GitHub App is not installed on the upstream repository
`open-goat/pequalnp-proofs`, which belongs to a third party. Every attempt to open a pull request
through the integration returns:

    POST https://api.github.com/repos/open-goat/pequalnp-proofs/pulls
    403 Resource not accessible by integration

That is GitHub refusing the app, not Claude refusing the action, so no Claude-side permission
change can lift it. Opening each pull request takes one click, or one command from a machine
where `gh` is signed in as KSXGitHub.

Each branch below is already pushed to https://github.com/KSXGitHub/pequalnp-proofs and holds
EXACTLY ONE new file that `lean` accepts with no `sorry` and that passes the tournament's format
rules. Nothing else is changed.

| branch | file | what it is | lean | open it |
|---|---|---|---|---|
| `R-meta-5266-1` | `lean/PEqualNP/Outside/R_meta_5266_1.lean` | reduction of L-meta-5266, the declared open core | CHECK_OK, no sorry, 3 permitted axioms | **SUBMITTED: [#10355](https://github.com/open-goat/pequalnp-proofs/pull/10355)** |

One command per row, from anywhere `gh` is signed in as KSXGitHub:

    gh pr create --repo open-goat/pequalnp-proofs --head KSXGitHub:R-meta-5266-1 --base main \
      --title 'R-meta-5266-1' --body ''

The pull request body is not read by the checker, so an empty body is fine.

## If you want this automated for the rest of the run

The published instructions (https://pequalnp.com/join.txt) expect `gh` signed in as the owner,
and say not to ask the owner for a token. The sanctioned route is therefore `gh auth login` in
this container, done by you through the device flow, which would put a credential of yours in a
throwaway cloud container - your call, and not something to do half asleep. Until then the loop
keeps proving and keeps appending rows here.
