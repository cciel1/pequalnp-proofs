import ConeBudget
import Saturated

namespace FanoMixedSize
open FanoBoundary PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Any monotone binary mixed core of at most thirteen gates which computes Fano incidence
from monotone pure features must receive, on one shore, all seven exact neighborhood ORs.
The witnesses are features of the original decomposition, for any number of original ports. -/
theorem thirteen_forces_exact_ors {a b : Nat} (C : Circuit) (hm : Monotone2 C) (budget : C.size ≤ 13)
    (P : Fin a → Input (Fin 7) → Bool) (L : Fin b → Input (Fin 7) → Bool)
    (hP : ∀ i, MonotoneFeature (P i)) (hL : ∀ j, MonotoneFeature (L j))
    (computes : ∀ x y, mixed C (fun i => P i x) (fun j => L j y) = true ↔
      AcceptsEdge incident x y) :
    (∀ l, ∃ i : Fin a, ∀ x, P i x = true ↔ ∃ p, incident p l ∧ x p = true) ∨
      (∀ p, ∃ j : Fin b, ∀ y, L j y = true ↔ ∃ l, incident p l ∧ y l = true) := by
  obtain ⟨u,v,points,lines,M,ht,hu,hv,hM,hcomp,hsize⟩ := restrict_mixed_ports C hm P L hP hL computes
  have eu : u = 7 := by omega
  have ev : v = 7 := by omega
  subst u
  subst v
  have classified := seven_each_forces_exact_ors (P ∘ points) (L ∘ lines)
    (fun i => hP _) (fun j => hL _) M hM hcomp hsize (by omega)
  rcases classified with left | right
  · left
    intro l
    obtain ⟨i,hi⟩ := left l
    exact ⟨points i,hi⟩
  · right
    intro p
    obtain ⟨j,hj⟩ := right p
    exact ⟨lines j,hj⟩

#print axioms thirteen_forces_exact_ors
end FanoMixedSize
