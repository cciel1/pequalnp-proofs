import BoundaryCount

namespace FanoMixedSize
open FanoBoundary

private theorem dual_inc : ∀ p l : Fin 7, incident p l ↔ incident (-l) (-p) := by decide

/-- Negating the coordinates exchanges the two shores of the desk's oriented
difference convention for the Fano plane. -/
theorem dual_accepts (x y : Input (Fin 7)) :
    AcceptsEdge incident (fun z => y (-z)) (fun z => x (-z)) ↔ AcceptsEdge incident x y := by
  constructor
  · rintro ⟨p,l,h,ha,hb⟩
    exact ⟨-l, -p, (dual_inc p l).mp h, hb, ha⟩
  · rintro ⟨p,l,h,ha,hb⟩
    exact ⟨-l,-p,(dual_inc p l).mp h, by simpa using hb, by simpa using ha⟩

theorem seven_features_each {a b : Nat}
    (P : Fin a → Input (Fin 7) → Bool) (L : Fin b → Input (Fin 7) → Bool)
    (hP : ∀ i, MonotoneFeature (P i)) (hL : ∀ i, MonotoneFeature (L i))
    (M : Input (Fin a) → Input (Fin b) → Bool) (hm : MixedMono M)
    (computes : ∀ x y, M (fun i => P i x) (fun j => L j y) = true ↔
      AcceptsEdge incident x y) : 7 ≤ a ∧ 7 ≤ b := by
  refine ⟨seven_point_features P L hP M hm computes, ?_⟩
  let lp (i : Fin b) (x : Input (Fin 7)) := L i (fun z => x (-z))
  let pl (i : Fin a) (y : Input (Fin 7)) := P i (fun z => y (-z))
  refine seven_point_features lp pl ?_ (fun l p => M p l) ?_ ?_
  · intro i x y hxy h
    exact hL i _ _ (fun z => hxy (-z)) h
  · intro x y l m hxy hl h
    exact hm _ _ _ _ hl hxy h
  · intro x y
    exact (computes (fun z => y (-z)) (fun z => x (-z))).trans (dual_accepts x y)

#print axioms seven_features_each
end FanoMixedSize
