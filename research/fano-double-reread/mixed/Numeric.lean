import Compression
import FanoFloor

namespace FanoMixedSize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity FanoBoundary

/-- A mixed circuit which computes Fano incidence on pure features with singleton
signatures has at least 20 gates, even when feature indices share the same raw wire. -/
theorem singleton_mixed_floor {a b : Nat} (C : Circuit) (hm : Monotone2 C)
    (P : Fin a → Input (Fin 7) → Bool) (L : Fin b → Input (Fin 7) → Bool)
    (hP : ∀ i, MonotoneFeature (P i)) (hL : ∀ j, MonotoneFeature (L j))
    (picks : Fin a → Fin 7) (lines : Fin b → Fin 7)
    (hp : ∀ i v, P i (one v) = true ↔ v = picks i)
    (hl : ∀ j v, L j (one v) = true ↔ v = lines j)
    (computes : ∀ x y, mixed C (fun i => P i x) (fun j => L j y) = true ↔
      AcceptsEdge incident x y) : 20 ≤ C.size :=
  FanoFloor.floor (raw_size C hm P L hP hL picks lines hp hl computes)

#print axioms singleton_mixed_floor
end FanoMixedSize
