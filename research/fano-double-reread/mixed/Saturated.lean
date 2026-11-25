import ExactNeighborhood
import BothShores
import FanoFloor

namespace FanoMixedSize
open FanoBoundary PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Bundle the two shores as the fourteen ports of the mixed computation. -/
def ports (M : Input (Fin 7) → Input (Fin 7) → Bool) (z : Input (Fin 14)) : Bool :=
  M (z ∘ Fin.castAdd 7) (z ∘ Fin.natAdd 7)

/-- The assumed realization of M may contain NOT gates; only the function M must be monotone. -/
theorem singleton_port_floor (P L : Fin 7 → Input (Fin 7) → Bool)
    (hP : ∀ i, MonotoneFeature (P i)) (hL : ∀ j, MonotoneFeature (L j))
    (M : Input (Fin 7) → Input (Fin 7) → Bool) (hm : MixedMono M)
    (computes : ∀ x y, M (fun i => P i x) (fun j => L j y) = true ↔ AcceptsEdge incident x y)
    (picks lines : Fin 7 → Fin 7)
    (hp : ∀ i p, P i (one p) = true ↔ p = picks i)
    (hl : ∀ j l, L j (one l) = true ↔ l = lines j)
    {s : Nat} (hc : HasCircuitSize 14 (ports M) s) : 20 ≤ s := by
  let π : Fin 14 → Fin 14 := Fin.append (fun i => Fin.castAdd 7 (picks i)) (fun j => Fin.natAdd 7 (lines j))
  have raw := Helpers.PermInputs.relabel_size π (ports M) s hc
  have eq : (fun z => ports M (z ∘ π)) = edge14 := by
    funext z
    let p : Input (Fin 7) := z ∘ Fin.castAdd 7
    let l : Input (Fin 7) := z ∘ Fin.natAdd 7
    have ep : (z ∘ π) ∘ Fin.castAdd 7 = (fun i => p (picks i)) := by funext i; simp [π, p]
    have el : (z ∘ π) ∘ Fin.natAdd 7 = (fun i => l (lines i)) := by funext j; simp only [Function.comp_apply, π, Fin.append_right, l]
    rw [ports, ep, el]
    apply Bool.eq_iff_iff.mpr
    have eqB := raw_singleton_features_compute_edge (List.finRange 7) (List.finRange 7)
      (by simp) (by simp) incident P L hP hL picks lines hp hl M hm computes p l
    simpa only [edge14, decide_eq_true_eq, AcceptsEdge, incident, p, l, Function.comp_apply] using eqB
  rw [eq] at raw
  exact FanoFloor.floor raw

/-- Negation exchanges the Fano coordinates of points and lines. -/
private def flip (x : Input (Fin 7)) : Input (Fin 7) := fun v => x (-v)

private theorem flip_flip (x : Input (Fin 7)) : flip (flip x) = x := by funext i; simp [flip]

private theorem flip_one (v : Fin 7) : flip (one v) = one (-v) := by
  funext u
  exact (by decide : ∀ u v : Fin 7, one v (-u) = one (-v) u) u v

private theorem flipped_hit (p : Fin 7) (y : Input (Fin 7)) :
    (∃ v, incident v (-p) ∧ flip y v = true) ↔ ∃ l, incident p l ∧ y l = true := by
  have dual : ∀ a b : Fin 7, incident a b ↔ incident (-b) (-a) := by decide
  constructor
  · rintro ⟨v,h,hy⟩
    exact ⟨-v,by simpa using (dual v (-p)).mp h,hy⟩
  · rintro ⟨l,h,hy⟩
    exact ⟨-l,(dual p l).mp h,by simpa [flip] using hy⟩

/-- At a budget below twenty, a monotone mixed computation on seven ports per shore forces
one full set of exact line ORs. The port-order witness may depend on the center. -/
theorem seven_each_forces_exact_ors (P L : Fin 7 → Input (Fin 7) → Bool)
    (hP : ∀ i, MonotoneFeature (P i)) (hL : ∀ j, MonotoneFeature (L j))
    (M : Input (Fin 7) → Input (Fin 7) → Bool) (hm : MixedMono M)
    (computes : ∀ x y, M (fun i => P i x) (fun j => L j y) = true ↔ AcceptsEdge incident x y)
    {s : Nat} (hc : HasCircuitSize 14 (ports M) s) (hs : s < 20) :
    (∀ l, ∃ i, ∀ x, P i x = true ↔ ∃ p, incident p l ∧ x p = true) ∨
      (∀ p, ∃ j, ∀ y, L j y = true ↔ ∃ l, incident p l ∧ y l = true) := by
  rcases seven_point_feature_rigidity P L hP M hm computes with ⟨ep,hp⟩ | ⟨ep,hp⟩
  · let L' (j : Fin 7) (x : Input (Fin 7)) := L j (flip x)
    let P' (i : Fin 7) (x : Input (Fin 7)) := P i (flip x)
    let M' (l p : Input (Fin 7)) := M p l
    have hL' (j : Fin 7) : MonotoneFeature (L' j) :=
      fun x y hxy h => hL j _ _ (fun i => hxy (-i)) h
    have hm' : MixedMono M' := fun _ _ _ _ hl hq h => hm _ _ _ _ hq hl h
    have corr (x y : Input (Fin 7)) : M' (fun j => L' j x) (fun i => P' i y) = true ↔
        AcceptsEdge incident x y := (computes (flip y) (flip x)).trans (dual_accepts x y)
    rcases seven_point_feature_rigidity L' P' hL' M' hm' corr with ⟨el,hl⟩ | ⟨el,hl⟩
    · exfalso
      apply (Nat.not_le_of_lt hs) (singleton_port_floor P L hP hL M hm computes ep (fun j => -(el j)) ?_ ?_ hc)
      · intro i p
        have e := congrArg (fun S : Finset (Fin 7) => p ∈ S) (hp i)
        simpa [pointSignature] using Iff.of_eq e
      · intro j l
        have e := congrArg (fun S : Finset (Fin 7) => -l ∈ S) (hl j)
        have w : L j (one l) = true ↔ -l = el j := by simpa [pointSignature, L', flip_one] using Iff.of_eq e
        exact w.trans ((by decide : ∀ a b : Fin 7, -a = b ↔ a = -b) l (el j))
    · right
      intro p
      let j := el.symm (-p)
      have ej : el j = -p := el.apply_symm_apply _
      refine ⟨j,fun y => ?_⟩
      have h := exact_neighborhood_features L' P' hL' M' hm' corr el hl j (flip y)
      rw [ej] at h
      change L j (flip (flip y)) = true ↔ _ at h
      rw [flip_flip] at h
      exact h.trans (flipped_hit p y)
  · left
    intro l
    let i := ep.symm l
    exact ⟨i, fun x => by simpa [i] using (exact_neighborhood_features P L hP M hm computes ep hp i x)⟩

#print axioms singleton_port_floor
#print axioms seven_each_forces_exact_ors
end FanoMixedSize
