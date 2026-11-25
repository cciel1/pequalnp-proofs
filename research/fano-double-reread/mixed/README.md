# Mixed gates in the Fano incidence circuit

A mixed gate has both a point and a line among the raw variables in its structural support. For a fan-in-two AND/OR circuit on the 14 inputs encoding the Fano incidence graph, the following statements have Lean proofs.

- At least 13 gates are mixed. If at most 13 are mixed, one shore supplies all seven three-variable neighborhood ORs. Realizing them requires at least 14 pure gates. Thus a circuit with at most 26 gates must have at least 14 mixed gates.
- The final adapter, `MixedExtract.Desk582.normalized_witness` in `Desk.lean`, starts with the exact edge labels and the fan-in-at-most-two model of L-meta-582. It produces a circuit of no greater size, in cyclic incidence coordinates and with exactly two earlier operands per gate, containing at least 14 mixed and at most 12 pure gates. This restricts a possible witness. The existence of such a witness remains open.
- In a circuit with at most 26 total gates and exactly 14 mixed gates, the mixed part reads seven distinct pure inputs from one shore and eight from the other. All fourteen mixed gates feed the result and no mixed subcircuit is shared. These statements are in `FourteenReal.lean` and `Tree.lean`.
- For the decomposition into pure point and line features followed by a mixed circuit, `FanoOrBudget.arbitrary_fano_budget` in `Arbitrary.lean` bounds 20 by the mixed-circuit size plus the sum of the OR costs of the distinct nonempty singleton supports. A support of size k costs k−1 gates. The numeric step uses the project's L-meta-5670.

From a checkout of this branch with the Lean 4.36.0 project dependencies installed, run `bash research/fano-double-reread/mixed/check.sh`. The final theorems print their axiom dependencies. This independent work also applies to the incidence function underlying L-meta-2348. It does not resolve its 27-gate derivative condition.
