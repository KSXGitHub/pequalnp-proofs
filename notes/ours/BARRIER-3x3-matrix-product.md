# Why the AND-counting route to the 3x3 Boolean product cannot work

Desk step L-meta-18919 asks for an AND/OR/NOT circuit of at most 44 fan-in-two gates computing the
3x3 Boolean matrix product. Schoolbook is 45 (27 AND + 18 OR). We held shard 9 of 16, "exactly 2 NOT
gates, 12 to 22 AND gates", and released it as `out_of_time` - NOT as `exhausted`, because we neither
found a witness nor emptied the range, and there is no program behind an exhaustion claim.

The reason to write this down is that the obvious opening is WRONG, and we verified that rather than
suspecting it. Anyone who picks up one of these sixteen shards will reach for the same argument.

## The obvious opening, and the barrier that kills it

The opening: "the nine outputs need the 27 distinct products x_{ik} AND y_{kj} between them, and our
shard caps ANDs at 22, so the range is empty." That argument consults only the size-2 prime-implicant
structure of the target - equivalently, only the rows of Hamming weight at most 2. THAT DATA IS
CONSISTENT WITH FIFTEEN AND GATES.

The witness, with 18 inputs x_{ik} and y_{kj}:

    X_k = OR_i x_{ik}        (3 gates worth of ORs each)
    Y_k = OR_j y_{kj}
    P_k = X_k AND Y_k
    Q   = OR_k P_k
    R_i = OR_k x_{ik}
    C_j = OR_k y_{kj}
    Q_i = Q AND R_i
    F_ij = Q_i AND C_j
    plus two NOT gates nothing reads

Measured, with two independent evaluators agreeing (column bitmasks, and a literal `foldl`/`getD`
row evaluator):

* size 43, 15 AND, 26 OR, 2 NOT - so it sits INSIDE shard 9's syntactic class;
* all nine outputs monotone over all 262144 rows;
* its size-<=2 prime implicants are EXACTLY the 27 products, on every output;
* 172 rows have weight <= 2 and it is correct on every one of them;
* its first disagreement with the target is at weight 3 (row 522).

So any argument that looks only at weight-<=2 structure cannot prove more than `>= 15` ANDs, which
is short of the needed 23 by eight. The ceiling of this trick scales as n^2 + 2n against the true
n^3: 8 vs 8 at n = 2 (no saving), 15 vs 27 at n = 3, 24 vs 64 at n = 4. The barrier therefore appears
for the FIRST time exactly at the size this step asks about. A proof must use rows of weight >= 3.

## The branch reduction also tops out one gate short

The natural way to handle a bounded number of NOT gates: put them in topological order, substitute
constants b in {0,1}^2 for the two NOT wires, and get four MONOTONE circuits C_b, each with at most
42 gates and exactly C's AND gates, each correct on its part, the four parts partitioning the cube.
A contradiction needs some part to force >= 23 ANDs.

It does not. For a splitting the circuit is free to choose - the two NOTs reading input wires x_{00}
and y_{00}, which costs no gates - every part is individually satisfiable with at most 22 ANDs:

    branch (0,0): 65536 rows, monotone circuit size 36, AND 20, OR 16, 0 wrong rows in the part
    branch (0,1): size 37, AND 22, OR 15, 0 wrong
    branch (1,0): size 37, AND 22, OR 15, 0 wrong
    branch (1,1): size 35, AND 22, OR 13, 0 wrong

Exactly one short of 23, so the route yields no contradiction for ANY shard whose AND cap is at least
22 - ours included. Plain pigeonhole over the 27 weight-2 rows gives only ceil(27/4) = 7.

## Where that leaves the step

Over the monotone basis exactly n^3 AND gates are necessary for the n x n Boolean product, and the
school method is UNIQUELY optimal among monotone circuits (Paterson 1975; Mehlhorn and Galil 1976).
So 45 is monotone-optimal at n = 3 and a 44-gate answer must beat a proven-optimal construction by a
net gate using negation. The literature has nothing finite for negation-limited circuits: the
nearest result gives an asymptotic AND-gate bound under a negation-dependent conjunction-depth
hypothesis, with no usable constant at n = 3.

What would actually settle these shards is a new theorem - "every fan-in-two AND/OR/NOT circuit with
at most 2 NOT gates computing the 3x3 Boolean product has at least 23 AND gates", or better
"ANDs + ORs >= 43", which would empty shards 8 to 11 at once. The branch reduction is the right
opening move, but the monotone fact it wants is false as shown above, so a proof has to use weight
>= 3 rows AND exploit that the four branch circuits are constant-substitutions of ONE circuit sharing
at most 22 ANDs and at most 42 non-NOT gates. That is a sharing argument, not a counting one.
Even the monotone shards 0 to 3 rest on a fifty-year-old paper proof whose finite part nobody has
reduced to a machine check; posting THAT as a step would be the sensible prerequisite for closing
any of the sixteen.

## Calibration, for honesty about what is and is not settled

At n = 2, where the question is decidable (monotone optimum 2n^3 - n^2 = 12), a multi-output encoder
validated against an existing solver-free brute force gave: full basis UNSAT at sizes 1 to 9,
SAT at 12 (the schoolbook, re-simulated on all 256 rows), monotone-only UNSAT at 10, and
"AND <= 7 with NOT <= 2" UNSAT at 9. Full basis at 10 and monotone at 11 DID NOT RETURN. So the
full-basis minimum at n = 2 lies between 10 and 12 and whether negation helps even there is open.
A timeout is "did not return", never UNSAT.
