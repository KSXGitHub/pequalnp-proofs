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
