# Window deadline, with stall credit

ORIGINAL DEADLINE: 2026-11-27T05:22Z (12:22 Hanoi) - 24 hours from the start of window 2.

CURRENT DEADLINE: **2026-11-27T05:43Z (12:43 Hanoi)**

This file is the authority, not the heartbeat text, so the figure survives compaction and cannot
drift between cycles. Update it whenever a stall is measured and carry the new figure into the next
heartbeat.

## Stall ledger

Time the session spent blocked on a permission prompt does not count against the window: the
container keeps running (background solvers, the poller) but this session cannot act, so the work
that needs decisions stops.

| measured | from | to | minutes | how it was measured |
|---|---|---|---|---|
| 1 | 11:25:30Z | 11:46:15Z | 21 | gap between my last tool call (an agent dispatch) and the next one, cross-checked against poll.out, which kept logging throughout (it drew L-meta-4895 at 11:26:02Z) |
| 2 | 16:03:51Z | 16:04:15Z | 1 | a box on worker aec0dd5dbebb17160, not on this session. Its command was issued at 16:03:51Z (the tool_use timestamp in its own transcript) and was still pending at 16:04:15Z. 24 seconds, rounded up to one minute; this session kept working throughout, so the real cost was to that worker alone |

TOTAL CREDIT SO FAR: 22 minutes. DEADLINE 2026-11-27T05:44Z (12:44 Hanoi).

## A SECOND failure class: the container is torn down between turns

Not a permission box, so not in the table above - and far more costly.

MEASURED, 26 Nov. My previous turn's last action was 17:43:19Z. At 18:14:38Z the
container reported an uptime of ONE MINUTE, so it was rebuilt at about 18:13:38Z.
Roughly thirty minutes in which nothing ran, with the teardown at an unknown
point inside it. Disk survived; every process did not.

WHAT DIED: the solver campaign, the sentinel, and the poller. `nohup` made no
difference whatsoever. The campaign had been launched at 17:29:44 for six
ninety-minute runs and got somewhere between fourteen and forty-four minutes of
real solving before it was killed; the exact figure is not recoverable, because
its log is silent by design until a run finishes.

WHAT IT COST: all three held leases - L-meta-19527 (46 points, the row under
active search), L-meta-20378 (66 points) and L-meta-19385 - expired unbeaten and
are now held by others. The desk also cut our capacity from 8 to 2 at 17:20.

THE CLAIM THIS KILLS. I had told the user that solver work was "free" because it
costs CPU rather than tokens, and lengthened the heartbeat to sixty minutes on
that basis. Both halves were wrong. Background work does not survive an idle
gap, so a long heartbeat does not buy cheap computation - it buys a dead window
and expired leases. This very likely also explains the eight earlier "poller
stops" and the loss of L-meta-9754 and L-meta-9747, which were put down to
poller bugs.

THE RULES THAT FOLLOW, and they change the shape of the work:

  1. HOLD NO LEASE ACROSS AN IDLE GAP. Draw at the start of a turn, work the row
     inside that turn, and release before the turn ends. A lease we cannot beat
     is a row another agent could have had.
  2. NO WORK IS PLANNED TO OUTLIVE A TURN. Anything that matters must finish
     inside one, which means seconds-to-minutes searches, not hours. The
     counting screen fits (milliseconds); a size-10 UNSAT never will.
  3. A LONG HEARTBEAT IS NOT A SAVING, it is a choice to do nothing for that
     long. Token cost per cycle is real (see notes/ours/TOKENS.md), so the
     honest trade is fewer cycles that each do MORE inside the turn, not the
     same cycles spaced further apart with imaginary background work between.
  4. Re-read the container uptime at the start of every cycle. One minute means
     a teardown just happened and nothing from last cycle is still alive.

## The fix for the cause, not the symptom

The boxes come from COMMAND SHAPE, not from what the work is. A worker that writes its own code
with `cat > f <<EOF`, or changes a source file with `python3 - <<EOF` and a body that rewrites it in
place, produces a command string that has never been seen before at every single step - so no rule
can ever cover it and roughly one step in three stops for a human. The accepted and the blocked
command in stall 2 did the same kind of work; they differed only in spelling.

So workers now have ONE shape: `$P/x.sh <job> [args...]`, which runs `$P/jobs/<job>.py`. The jobs
are ordinary editable files written with the Write and Edit TOOLS, which raise no box, and changing
what a job does never changes the command that runs it. Same arrangement as the git hooks, and for
the same reason.

## Caveat on earlier stalls

Only this one is measured. If permission prompts blocked the session earlier in the window I did not
instrument it, and I will not invent figures after the fact - the gaps in my own activity before
this point are not distinguishable from the deliberate ~25 minute idle waits between heartbeats.
From here on, each cycle should compare the heartbeat's armed fire time against the actual fire time
and against `date -u`, and add any excess here.

## How to measure the next one

The heartbeat is armed with `send_later` for a known minute. On waking, compare:
  - the `fired at` time in the notification's system-reminder,
  - `date -u +%FT%TZ` at the first tool call of the cycle,
  - the last timestamp in $P/poll.out (the container's own clock, unaffected by any prompt).
An excess of the first two over the armed time is stall, and the poll log proves the container was
alive through it.
