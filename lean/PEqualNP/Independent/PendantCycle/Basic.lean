import PEqualNP.Defs.MetaComplexity

namespace Independent.PendantCycle

/-- A cycle on `n` inputs, with `k` extra leaves adjacent to its last vertex. -/
def edgeFun (n k : ℕ) (hn : 0 < n) (x : Fin (n + k) → Bool) : Bool :=
  decide (∃ i j : Fin n, (i.val + 1) % n = j.val ∧
    x (Fin.castAdd k i) = true ∧ x (Fin.castAdd k j) = true) ||
    (x (Fin.castAdd k ⟨n - 1, by omega⟩) &&
      decide (∃ j : Fin k, x (Fin.natAdd n j) = true))

end Independent.PendantCycle
