# Exact circuit size of a cycle with pendant leaves

Independent Lean formalization by **cciel1**, developed with OpenAI Codex. Published on 25 November 2026 in the contributor's research branch.

## Result

Take a cycle on `n ≥ 5` vertices and attach `k ≥ 0` new leaves to one cycle vertex. Give each vertex a Boolean input. The output is true precisely when both endpoints of at least one edge are true. The minimum number of gates computing this function is

$$n + \lceil n/2 \rceil + k - 1.$$

The circuit model allows AND, OR and NOT, with at most two input wires per gate. Inputs are free and each gate counts once. For example, a pentagon with two leaves at the same vertex needs exactly nine gates. [Model](../../lean/PEqualNP/Defs/MetaComplexity.lean) · [Graph function](../../lean/PEqualNP/Independent/PendantCycle/Basic.lean) · [Exact theorem](../../lean/PEqualNP/Independent/PendantCycle/Exact.lean)

## Proof

**Lower bound.** Fix the input of one leaf to false. The restricted function computes the graph with that leaf deleted and remains nonconstant. The leaf is an essential input because switching it on changes the output when the hub is the only active vertex. Gate elimination therefore removes at least one gate per leaf. After all `k` restrictions, the remaining circuit must meet the known lower bound for the bare cycle. [Formal lower bound](../../lean/PEqualNP/Independent/PendantCycle/Lower.lean) · [Gate elimination](../../lean/PEqualNP/MetaComplexity/L014.lean) · [Exact cycle theorem](../../lean/PEqualNP/MetaComplexity/L106.lean)

**Upper bound.** Removing the hub from the cycle leaves a path. Use the existing path circuit for the path's edges. Separately OR together the hub's two cycle neighbors and its `k` leaves, AND that result with the hub, then OR the two outputs. The neighbor OR chain grows by exactly one gate per leaf. The Lean proof constructs the circuit and verifies its behavior on every input. [Formal construction](../../lean/PEqualNP/Independent/PendantCycle/Upper.lean) · [Path circuit](../../lean/PEqualNP/MetaComplexity/Helpers/CyclePathGates.lean)

## Relation to prior work

The contribution here is one checked theorem covering every `n ≥ 5` and `k ≥ 0`, including cycles of lengths five and six. For `k = 0`, the formula is the project's bare-cycle theorem. For `n ≥ 7`, the same value also follows mathematically from the project's long-thread lower bound and vertex-cover upper bound. The only cycle has length `n`, there is at most one vertex of degree three or more, and one can choose a minimum cycle cover containing the hub. The six-cycle with one leaf already appears in an upstream proof. [Project research note](../../notes/note-1-edge-function-exact-size.md) · [Long-thread lower bound](../../lean/PEqualNP/MetaComplexity/L204.lean) · [Vertex-cover upper bound](../../lean/PEqualNP/MetaComplexity/L105.lean) · [Earlier six-cycle example](../../lean/PEqualNP/Outside/L_meta_8487.lean#L8-L9)

## Leaves attached at several vertices

Let `G` be a finite simple graph with at least one edge, and `T` a vertex cover whose bound is tight for `G`. Thus its minimum circuit size is `|E(G)| + |T| - 1`. Attach `k` fresh degree-one vertices, each to any vertex in `T`. Several leaves may share an anchor. The new minimum is exactly the old minimum plus `k`. [Theorem and proof](../../lean/PEqualNP/Independent/LeafExtension/Exact.lean)

The lower bound applies to arbitrary anchors by restricting leaf inputs one at a time. For the upper bound, `T` still covers every edge and each attachment adds one edge, so the project's vertex-cover construction matches the lower bound. This gives a way to extend a previously tight base graph without repeating the circuit analysis after each attachment. [Graph construction](../../lean/PEqualNP/Independent/LeafExtension/Graph.lean) · [Restriction lemma](../../lean/PEqualNP/Independent/LeafExtension/Lower.lean) · [Cover lemma](../../lean/PEqualNP/Independent/LeafExtension/Cover.lean)

## Reproduce the check

With Git and elan installed, the checkout selects Lean 4.36.0 and the pinned Mathlib revision. The cache command downloads precompiled dependencies. The build then checks the research modules.

```sh
git clone --single-branch --branch research/pendant-cycles https://github.com/cciel1/pequalnp-proofs.git
cd pequalnp-proofs/lean
lake exe cache get
lake build +PEqualNP.Independent.PendantCycle.Exact +PEqualNP.Independent.LeafExtension.Exact
printf '%s\n' 'import PEqualNP.Independent.PendantCycle.Exact' '#print axioms Independent.PendantCycle.exact_size' | lake env lean --stdin
printf '%s\n' 'import PEqualNP.Independent.LeafExtension.Exact' '#print axioms Independent.LeafExtension.min_size_attach' | lake env lean --stdin
```

Run the two audit commands separately. At this upstream revision, the bare-cycle and vertex-cover libraries both declare `PEqualNP.MetaComplexity.Helpers.getD_ofFn` in different modules, so importing both libraries in a single Lean file produces a name collision. Each audit reports `propext`, `Classical.choice` and `Quot.sound`. The research modules build on [upstream revision `8e683929`](https://github.com/open-goat/pequalnp-proofs/commit/8e6839295f2f4f87496af759e8b0f2e894d0f114).
