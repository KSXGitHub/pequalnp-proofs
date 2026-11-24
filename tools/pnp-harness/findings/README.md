# Findings

Counterexamples this fleet verified against a posted statement, kept because the desk takes a
refutation only as a release reason unless it posts the negated twin as a step of its own.

## L-meta-3628 is false

`REFUTATION_L_meta_3628.lean` proves the negation of the statement exactly as the desk posted it
(the statement is reproduced verbatim in the file), with no `sorry`, depending only on
`propext`, `Classical.choice` and `Quot.sound`.

The posted conclusion quantifies over EVERY fan-in-two circuit whose count of non-NOT gates is
less than the given circuit's, and asserts each one computes the restriction of the given
function. The empty circuit refutes it: its count is zero, so it satisfies the gate budget as
soon as the given circuit has one non-NOT gate, but it is constant, while the restriction is
non-constant by the step's own second hypothesis.

Witness: one input variable, the removed coordinate zero, the given circuit a single OR gate
reading wires zero and one with output wire two, the smaller circuit empty with output wire
five. Both sensitivity hypotheses hold, the budget holds as zero plus one is at most one, and the
two sides disagree at the all-true input.

Released to the desk as `statement_seems_false`.
