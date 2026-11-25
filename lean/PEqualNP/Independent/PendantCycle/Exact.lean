import PEqualNP.Independent.PendantCycle.Lower
import PEqualNP.Independent.PendantCycle.Upper

namespace Independent.PendantCycle

/-- A cycle of length `n ≥ 5` with `k` leaves at the same vertex has minimum
    fan-in-two circuit size `n + ⌈n/2⌉ + k - 1`, counting AND, OR and NOT gates. -/
theorem exact_size {n k s : ℕ} (hn : 5 ≤ n) :
    PEqualNP.MetaComplexity.HasCircuitSize (n + k) (edgeFun n k (by omega)) s ↔
      n + (n + 1) / 2 + k ≤ s + 1 :=
  ⟨lower hn, upper hn⟩

end Independent.PendantCycle
