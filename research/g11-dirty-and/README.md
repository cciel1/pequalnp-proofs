# Three dirty AND gates for G11

`G11Control22.lean` verifies a concrete circuit for the graph in L-meta-8031. It uses 22 gates, accepts the 16 edge inputs, and rejects all 24 maximal independent inputs. Gates 3, 9 and 16 are AND gates that accept independent inputs. All three contribute to the output. The file changes only the gate-count limit in the requested proposition. `gates22.json` gives the zero-based wire list with 0 for OR and 1 for AND.

The separator vertices 9 and 10 divide the edge set into two subgraphs. `RightChild.lean` verifies the exact six-gate, one-dirty-AND certificate for the five-vertex subgraph. The eight-vertex subgraph has a 15-gate, two-dirty-AND construction in `SideCertificates.lean`. One final OR joins the subcircuits. A 14-gate realization of the latter subgraph satisfying the same conditions would suffice to settle the 21-gate step.

Use the repository's Lean 4.36 toolchain. From `lean/`, run `lake build PEqualNP.Outside.L_meta_8608`, then `lake env lean ../research/g11-dirty-and/G11Control22.lean`. The two certificate files can be checked in the same way.
