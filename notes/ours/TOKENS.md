# Token ledger

The authority on what this session has cost and what each thing costs per unit.
Kept in the repository because it has to survive context compaction and the
container, and because the next datapoint is only useful next to this one.

## Datapoints given by the user

| when | figure | note |
|---|---|---|
| 2026-11-26 ~17:30Z | **over 39% of weekly tokens used** | across several tasks, not only this one; the user suspects this one contributed the most |

When the next figure arrives, the per-task average follows from the delta:
divide the change in percent by the work done between the two datapoints, using
the counters below. Record the new figure in this table rather than in a reply,
so a later session can still do the arithmetic.

## Measured, not estimated

Every assistant record in a Claude Code transcript carries a `usage` object for
that one request. `engines/jobs/tokens.py` sums them. Numbers as of
2026-11-26 17:35Z:

| | main thread | 71 agents | total |
|---|---|---|---|
| requests | 4,681 | 7,835 | 12,516 |
| uncached input | 12,885,330 | 73,573,484 | **86,458,814** |
| cache read | 2,221,182,128 | 1,408,323,403 | **3,629,505,531** |
| output | 6,616,925 | 17,091,008 | **23,707,933** |

Do not collapse these into one number: cache reads are billed at a fraction of
fresh input, and only the account knows the rates. But the orders of magnitude
settle the question of where the money went.

## The one fact that matters

**Cache read dominates everything.** 3.63 billion against 86 million uncached.
Even at a tenth of the rate it is several times the entire uncached bill.

And cache read is driven by REQUEST COUNT, not by how much is written, because
every request re-reads the whole conversation prefix:

| | per request | why it is that big |
|---|---|---|
| main thread | **~474,000 cache-read tokens** | a long conversation; the prefix is re-read every time |
| an agent | ~180,000 cache-read tokens | shorter context, so about 2.6x cheaper per call |

So **one tool call on the main thread costs about 474k cache-read tokens**,
whatever it does. `ls` costs the same as a full build. That is the single most
important number here and it reframes the whole approach: the expensive thing is
not the work, it is the number of times I come back to look at it.

Per agent, averaged over 71: 1.04M uncached input, 19.8M cache read, 241k output.
Mean cost by uncached input plus output is 1.28M, median 753k - the mean is well
above the median because a handful of long agents dominate (the largest single
one is 9.2M).

Agents account for **85% of uncached input** and 39% of cache read.

## What follows, in order of saving

1. **Fewer main-thread tool calls.** Batch independent calls into one message,
   and stop confirming things already known. At ~474k a call this is the biggest
   lever by a wide margin, and 4,681 calls is where the session went.
2. **Longer gaps between heartbeat cycles.** Each cycle is roughly ten to twenty
   calls, so five to ten million cache-read tokens. A cycle that finds nothing
   new costs the same as one that settles a row.
3. **Fewer agents, and briefed to be short.** 191k of new tokens each at the
   harness's own accounting, far more by cache read. An agent is worth it when
   it would take many main-thread calls to do the same thing - which is often
   true, since its calls are 2.6x cheaper - but not for anything a single
   command answers.
4. **Prefer CPU to tokens wherever the question is computational.** The queued
   solver campaign (`engines/jobs/campaign.py`) runs three cores continuously
   for zero tokens. Everything that can be pushed into it should be.

## Counters to carry forward

Re-run `engines/jobs/tokens.py` at the next datapoint and append a row here.
What to record each time: the four usage totals for main and agents, the agent
count, and the number of heartbeat cycles since the last entry.

## Second datapoint, and the conversion it gives

| when | figure |
|---|---|
| 2026-11-26 17:30Z | 39% of weekly tokens used |
| 2026-11-27 04:25Z | **41%** |

Two percentage points over 10.9 hours, and the window is unusually clean for
measurement: **632 tool calls, every one on the main thread, zero agents
spawned.** So the delta attributes to one kind of work.

| | measured delta | per 1% of week | implied week (lower bound) |
|---|---|---|---|
| tool calls | 632 | 316 | 31,600 |
| cache read | 404,485,719 | 202,242,860 | 20,224,285,950 |
| uncached input | 2,661,473 | 1,330,736 | 133,073,650 |
| output | 766,252 | 383,126 | 38,312,600 |
| rows settled | 60 | 30 | - |

**One main-thread tool call = 0.00316% of the week** (about 640,000 cache-read
tokens). **One desk row settled = 0.0333%**, about 10.5 calls each.

### The marginal call costs more than the average one

The session average was about 474,000 cache-read tokens per call. This window's
MARGINAL cost is 640,000 - 35% higher - because every call re-reads a longer
conversation. The same work costs more the later in a session it happens, and
that gap will keep widening. It is the strongest argument for batching and for
not reopening settled questions.

### Agents are not the only expensive thing

The first 39% was agent-dominated: 71 agents, 83% of all uncached input. This
window spawned NO agent and still cost two points. Sustained main-thread
looping is comparable to agent work, which corrects the earlier framing that
agents were the problem. The lever is CALL COUNT, wherever the calls happen.

### Attribution, with its assumption stated

Converting the whole session at this window's rate, and taking cache reads to
bill at roughly a tenth of fresh input (the real ratio is not known here):
4.03 billion cache read plus 89 million uncached is about **23% of the weekly
budget for this session**, leaving roughly 18% across all other tasks in the
same week.

CAVEAT, and its direction is known while its size is not: the two points cover
EVERY task on the account, not only this one. Anything else running in the
window makes this session's share less than two points, which makes the weekly
budget larger than estimated and every per-unit figure above an OVER-estimate.
The only other scheduled task on the account fires once a day and is tiny, so
the error is probably small.

### To extend the series

Record the next percentage here with the output of `engines/jobs/tokens.py` at
the same moment. Two datapoints give a rate; three show whether the rate is
drifting, which it should be - upward, as the conversation grows.

### Where this file lives, since I got it wrong twice

`notes/ours/TOKENS.md` is the ONLY copy and it is edited in the repository
directly. It is NOT under `notes/ours/engines/`, so `rescue.py` neither copies
nor overwrites it - and `rescue.py`'s file list does not mention it at all.
Appending to a scratchpad `TOKENS.md` therefore writes to a file nothing reads,
and the commit afterwards reports "nothing to commit, working tree clean",
which looks like success.

The rule that covers both traps: anything under `notes/ours/engines/` is edited
in the SCRATCHPAD and carried over by rescue; anything else under `notes/ours/`
is edited in the REPOSITORY. Check which before appending.
