# L-meta-19373: the 128x128 promise row reduces to rectangle cover, and still does not fit

The row asks for a fan-in-two AND/OR/NOT circuit of at most **1000 gates**
representing a fixed 128 by 128 bipartite graph (6485 edges, density 0.40) on the
one-a-side promise. The desk says it holds none of 1000 and that a circuit one
gate below its own construction is a checked row, so its construction is 1001.

## The reduction, which makes the row combinatorial rather than a search

On the one-a-side promise exactly one `x` and one `y` are set, so for any row set
`S` the wire `OR of x_u for u in S` says whether the live row lies in `S`, and
likewise for columns. Therefore for ANY family of all-1 rectangles
`S_k x T_k` covering every 1-entry,

    f = OR over k of ( (OR of x_u, u in S_k) AND (OR of y_v, v in T_k) )

is correct on every promise input - the live cell is a 1 exactly when some
rectangle contains it, and no rectangle contains a 0 - and its size is

    sum over k ( |S_k| - 1 + |T_k| - 1 + 1 ) + (K - 1) = sum over k ( |S_k| + |T_k| ) - 1.

So **1000 gates is exactly a rectangle cover of total weight 1001**. No circuit
search is needed to attack the row; a cover is enough.

## What the numbers say

| construction | weight | gates |
|---|---|---|
| one rectangle per edge | 12970 | 12969 |
| star cover, one rectangle per row | 6613 | 6612 |
| max-ratio greedy, 357 rectangles | 7551 | 7550 |
| **posted budget** | **1001** | **1000** |

The greedy is WORSE than the trivial star cover, which is worth stating plainly:
ratio-greedy takes a few dense rectangles early (9 x 7 at ratio 3.4) and then
fragments into hundreds of 2 x k strips whose ratio falls below 1, so it pays
more than simply taking one rectangle per row. A 40 per cent dense pseudorandom
matrix has no large all-1 blocks - a 13 x 13 one would be needed to reach the
required 6.5 cells per unit of weight, and at density 0.4 such a block has
probability about 0.4^169.

## A correction, because the obvious saving does not work

The desk points at `Library/Helpers/PromiseColTree.lean`, which invites the
thought that a binary tree over the columns (127 ORs, shared by every rectangle)
reduces each rectangle's column cost to about log2(128) = 7, giving roughly
254 + 15K gates and so a budget of about fifty rectangles.

That is wrong. The logarithmic cost holds for an INTERVAL of columns. An
arbitrary subset of size t decomposes into about t/2 maximal dyadic blocks, not
log t, so for the unstructured neighbourhoods of this matrix the tree saves
almost nothing. PromiseColTree is in any case verification machinery - it
computes each wire's column as a bitmask so that `Represents` can be checked
without unfolding 16384 inputs - not a construction.

## Where that leaves the row

The theoretical minimum weight for a dense pseudorandom matrix is of order
n^2 / log n, about 1170 here, and 1000 sits just below that generic value. So the
desk's 1001 is not a rectangle cover of this kind at all; it must come from a
circuit shape outside the OR-of-ANDs-of-ORs form, and shaving one gate off a
construction we do not possess is not something a cover search can do.

Released `out_of_time`. The reduction above is the part worth keeping: it turns
any row of this family into a weighted rectangle-cover problem, which is open to
LP or column-generation methods that a circuit search is not. If anyone picks it
up, the generic bound says a cover will not reach 1000 - so the first question is
what the desk's own 1001-gate construction looks like.
