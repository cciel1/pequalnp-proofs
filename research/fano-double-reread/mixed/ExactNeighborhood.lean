import SevenRigidity

namespace FanoMixedSize
open FanoBoundary

/-- The largest point assignment containing no point of the specified line. -/
def outsideLine (l : Fin 7) : Input (Fin 7) := fun p => decide (¬incident p l)

/-- At least one provider of a flag must distinguish its singleton point from the entire
complement of its line, for the fixed line-side assignment containing that line alone. -/
theorem rejecting_provider {a b : Nat}
    (P : Fin a → Input (Fin 7) → Bool) (L : Fin b → Input (Fin 7) → Bool)
    (hP : ∀ i, MonotoneFeature (P i)) (M : Input (Fin a) → Input (Fin b) → Bool)
    (hm : MixedMono M) (computes : ∀ x y, M (fun i => P i x) (fun j => L j y) = true ↔
      AcceptsEdge incident x y) {p l : Fin 7} (inc : incident p l) :
    ∃ i, (p,l) ∈ supportedFlags (pointSignature P i) ∧ P i (outsideLine l) ≠ true := by
  classical
  have pos := (computes (one p) (one l)).mpr ⟨p,l,inc,by simp [one],by simp [one]⟩
  have neg : ¬ AcceptsEdge incident (outsideLine l) (one l) := by
    rintro ⟨q,t,hqt,hq,ht⟩
    have e : t = l := of_decide_eq_true ht
    exact (of_decide_eq_true hq) (e ▸ hqt)
  have diff : ∃ i, P i (one p) = true ∧ P i (outsideLine l) ≠ true := by
    by_contra! h
    exact neg ((computes _ _).mp (hm _ _ _ _ h (fun _ h => h) pos))
  obtain ⟨i, hi, hout⟩ := diff
  refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, inc⟩, ?_⟩, hout⟩
  refine ⟨by simpa [pointSignature] using hi, ?_⟩
  intro q hq
  by_contra hc
  have hq' : P i (one q) = true := (Finset.mem_filter.mp hq).2
  exact hout (hP i _ _ (one_below (by simpa [outsideLine] using hc : outsideLine l q = true)) hq')

/-- With seven point features, a feature that provides a flag rejects any point assignment
avoiding that flag's line. This statement applies to either of the two possible shapes. -/
theorem provider_hits_line {b : Nat}
    (P : Fin 7 → Input (Fin 7) → Bool) (L : Fin b → Input (Fin 7) → Bool)
    (hP : ∀ i, MonotoneFeature (P i)) (M : Input (Fin 7) → Input (Fin b) → Bool)
    (hm : MixedMono M) (computes : ∀ x y, M (fun i => P i x) (fun j => L j y) = true ↔
      AcceptsEdge incident x y) {i p l : Fin 7} (provides : (p,l) ∈ supportedFlags (pointSignature P i))
    (x : Input (Fin 7)) (hx : P i x = true) : ∃ q, incident q l ∧ x q = true := by
  classical
  have inc : incident p l := (Finset.mem_filter.mp (Finset.mem_filter.mp provides).1).2
  obtain ⟨j, hj, hout⟩ := rejecting_provider P L hP M hm computes inc
  have eq := (seven_flag_partition _ (flag_coverage P L hP M hm computes)).2 i j _ provides hj
  subst j
  by_contra! h
  apply hout (hP i x _ ?_ hx)
  intro q hq
  apply decide_eq_true
  exact fun inc => h q inc hq

/-- A single row with full neighborhood signature must be exactly the OR of that neighborhood
on every assignment, including assignments with several active points. -/
theorem exact_neighborhood_row {b : Nat}
    (P : Fin 7 → Input (Fin 7) → Bool) (L : Fin b → Input (Fin 7) → Bool)
    (hP : ∀ i, MonotoneFeature (P i)) (M : Input (Fin 7) → Input (Fin b) → Bool)
    (hm : MixedMono M) (computes : ∀ x y, M (fun i => P i x) (fun j => L j y) = true ↔
      AcceptsEdge incident x y) {i t : Fin 7} (shape : pointSignature P i = neighborhood t)
    (x : Input (Fin 7)) : P i x = true ↔ ∃ p, incident p t ∧ x p = true := by
  have itt : incident t t := Or.inl rfl
  have prov : (t,t) ∈ supportedFlags (pointSignature P i) := by
    rw [shape]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,itt⟩, ?_⟩
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,itt⟩, fun q hq => (Finset.mem_filter.mp hq).2⟩
  constructor
  · exact provider_hits_line P L hP M hm computes prov x
  · rintro ⟨p,inc,hx⟩
    have mem : p ∈ pointSignature P i := shape ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _,inc⟩
    exact hP i _ _ (one_below hx) (Finset.mem_filter.mp mem).2

theorem exact_neighborhood_features {b : Nat}
    (P : Fin 7 → Input (Fin 7) → Bool) (L : Fin b → Input (Fin 7) → Bool)
    (hP : ∀ i, MonotoneFeature (P i)) (M : Input (Fin 7) → Input (Fin b) → Bool)
    (hm : MixedMono M) (computes : ∀ x y, M (fun i => P i x) (fun j => L j y) = true ↔
      AcceptsEdge incident x y) (e : Equiv.Perm (Fin 7))
    (shapes : ∀ i, pointSignature P i = neighborhood (e i)) :
    ∀ i x, P i x = true ↔ ∃ p, incident p (e i) ∧ x p = true :=
  fun i x => exact_neighborhood_row P L hP M hm computes (shapes i) x

#print axioms exact_neighborhood_features
end FanoMixedSize
