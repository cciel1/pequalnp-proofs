import Compression

namespace FanoMixedSize
open FanoBoundary

/-- The flag consisting of point p and line l must be distinguished from the
negative input consisting of l and all points outside its neighborhood. -/
theorem distinguishing_feature {α β ι κ : Type} [DecidableEq α] [DecidableEq β]
    (E : α → β → Prop) [DecidableRel E] (P : ι → Input α → Bool) (L : κ → Input β → Bool)
    (hP : ∀ i, MonotoneFeature (P i)) (M : Input ι → Input κ → Bool) (hm : MixedMono M)
    (exactOn : ∀ x y, M (fun i => P i x) (fun j => L j y) = true ↔ AcceptsEdge E x y)
    {p : α} {l : β} (edge : E p l) :
    ∃ i, P i (one p) = true ∧ ∀ q, P i (one q) = true → E q l := by
  classical
  let outside : Input α := fun q => decide (¬ E q l)
  have hn : ¬ AcceptsEdge E outside (one l) := by
    rintro ⟨q, t, e, hq, ht⟩
    have ht' : t = l := of_decide_eq_true ht
    exact (of_decide_eq_true hq) (ht' ▸ e)
  have hy := (exactOn (one p) (one l)).mpr
    ⟨p, l, edge, by simp [one], by simp [one]⟩
  have diff : ∃ i, P i (one p) = true ∧ P i outside ≠ true := by
    by_contra! h
    apply hn
    exact (exactOn outside (one l)).mp (hm _ _ _ _ h (fun _ h => h) hy)
  obtain ⟨i, hi, hout⟩ := diff
  refine ⟨i, hi, fun q hq => ?_⟩
  by_contra hne
  exact hout (hP i _ _ (one_below (by simpa [outside] using hne : outside q = true)) hq)

instance incDec : DecidableRel incident := fun p l =>
  inferInstanceAs (Decidable (p = l ∨ p = l + 1 ∨ p = l + 3))

def flagSet : Finset (Fin 7 × Fin 7) := Finset.univ.filter fun e => incident e.1 e.2

def supportedFlags (S : Finset (Fin 7)) : Finset (Fin 7 × Fin 7) :=
  flagSet.filter fun e => e.1 ∈ S ∧ ∀ q ∈ S, incident q e.2

theorem flagSet_card : flagSet.card = 21 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem flag_cap : ∀ S : Finset (Fin 7), (supportedFlags S).card ≤ 3 := by decide +kernel

def pointSignature {a : Nat} (P : Fin a → Input (Fin 7) → Bool) (i : Fin a) : Finset (Fin 7) :=
  Finset.univ.filter (fun p => P i (one p) = true)

theorem flag_coverage {a b : Nat}
    (P : Fin a → Input (Fin 7) → Bool) (L : Fin b → Input (Fin 7) → Bool)
    (hP : ∀ i, MonotoneFeature (P i)) (M : Input (Fin a) → Input (Fin b) → Bool)
    (hm : MixedMono M) (computes : ∀ x y, M (fun i => P i x) (fun j => L j y) = true ↔
      AcceptsEdge incident x y) :
    flagSet ⊆ Finset.univ.biUnion (fun i => supportedFlags (pointSignature P i)) := by
  classical
  intro e he
  have hinc : incident e.1 e.2 := (Finset.mem_filter.mp he).2
  obtain ⟨i, htrue, hsupport⟩ := distinguishing_feature incident P L hP M hm computes hinc
  refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨he, ?_⟩⟩
  exact ⟨by simpa [pointSignature] using htrue, fun q hq => hsupport q (by simpa [pointSignature] using hq)⟩

/-- Each point-side feature can account for at most three flags, so every
monotone decomposition of the Fano incidence function uses at least seven. -/
theorem seven_point_features {a b : Nat}
    (P : Fin a → Input (Fin 7) → Bool) (L : Fin b → Input (Fin 7) → Bool)
    (hP : ∀ i, MonotoneFeature (P i)) (M : Input (Fin a) → Input (Fin b) → Bool)
    (hm : MixedMono M) (computes : ∀ x y, M (fun i => P i x) (fun j => L j y) = true ↔
      AcceptsEdge incident x y) : 7 ≤ a := by
  classical
  let S := pointSignature P
  have sub : flagSet ⊆ Finset.univ.biUnion (fun i => supportedFlags (S i)) :=
    flag_coverage P L hP M hm computes
  have hcard := Finset.card_le_card sub
  have hsum := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin a)))
    (t := fun i => supportedFlags (S i))
  have hbound : (∑ i : Fin a, (supportedFlags (S i)).card) ≤ ∑ _i : Fin a, 3 :=
    Finset.sum_le_sum fun i _ => flag_cap (S i)
  rw [flagSet_card] at hcard
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hbound
  omega

#print axioms seven_point_features
end FanoMixedSize
