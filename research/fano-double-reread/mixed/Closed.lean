import Factor

namespace MixedExtract
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers

/-- All kept gates read only other kept wires, including primary wires. -/
def Closed (k : Nat → Bool) (i : Nat) : List Gate → Prop
  | [] => True
  | g :: gs => (k i = true → ∀ j ∈ g.inputs, k j = true) ∧ Closed k (i+1) gs

def MapsKept (k : Nat → Bool) (w v : List Bool) (r : Nat → Nat) : Prop :=
  ∀ j < w.length, k j = true → r j < v.length ∧ v.getD (r j) false = w.getD j false

private theorem append_read {w : List Bool} (v : Bool) {j : Nat} (h : j < w.length) :
    (w ++ [v]).getD j false = w.getD j false := List.getD_append _ _ _ _ h

private theorem append_last (w : List Bool) (v : Bool) : (w ++ [v]).getD w.length false = v := by simp

/-- All retained wires of a structurally closed subcircuit are evaluated correctly.
No output selection is needed; this simultaneously preserves every pure output. -/
theorem simulate_closed (k : Nat → Bool) (d : Nat → Nat) (gs : List Gate)
    (w v : List Bool) (r : Nat → Nat)
    (hm : MapsKept k w v r) (hb : Back w.length gs) (hc : Closed k w.length gs) :
    let p := compile k d w.length v.length r gs
    MapsKept k (gs.foldl step w) (p.1.foldl step v) p.2 := by
  induction gs generalizing w v r with
  | nil => exact hm
  | cons g gs ih =>
    obtain ⟨hbefore, hback⟩ := hb
    obtain ⟨hparents, hrest⟩ := hc
    have len : (step w g).length = w.length + 1 := by simp [step]
    cases hk : k w.length with
    | false =>
      have hr : MapsKept k (step w g) v (put r w.length (d w.length)) := by
        intro j hj hkeep
        rw [len] at hj
        have hne : j ≠ w.length := fun e => Bool.noConfusion (hkeep.symm.trans (e ▸ hk))
        have hj' : j < w.length := by omega
        simpa only [put, ite_eq_right hne, step, append_read _ hj'] using hm j hj' hkeep
      simpa only [compile, hk, Bool.false_eq_true, ite_false, List.foldl_cons, len] using
        ih (step w g) v (put r w.length (d w.length)) hr (len ▸ hback) (len ▸ hrest)
    | true =>
      let g' := renameGate r g
      have he : gateValue v g' = gateValue w g := by
        apply congrArg g.op.eval
        simp only [g', renameGate, List.map_map]
        exact List.map_congr_left fun j hj => (hm j (hbefore j hj) (hparents hk j hj)).2
      have len' : (step v g').length = v.length + 1 := by simp [step]
      have hr : MapsKept k (step w g) (step v g') (put r w.length v.length) := by
        intro j hj hkeep
        rw [len] at hj
        by_cases e : j = w.length
        · subst j
          exact ⟨by simp [put, len'], by simpa only [put, ite_true, step, append_last] using he⟩
        · have hj' : j < w.length := by omega
          obtain ⟨hjv, hval⟩ := hm j hj' hkeep
          exact ⟨by simp [put, e, len']; omega, by
            simpa only [put, ite_eq_right e, step, append_read _ hj', append_read _ hjv] using hval⟩
      simpa only [compile, hk, ite_true, List.foldl_cons, len, len', g'] using
        ih (step w g) (step v g') (put r w.length v.length) hr (len ▸ hback) (len ▸ hrest)

private theorem support_old {n} (gs : List Gate) (L : List (Finset (Fin n)))
    (j : Nat) (h : j < L.length) : (suppsFrom gs L).getD j ∅ = L.getD j ∅ := by
  induction gs generalizing L with
  | nil => rfl
  | cons g gs ih =>
    change (suppsFrom gs (L ++ [gateSupp L g])).getD j ∅ = _
    rw [ih _ (by simp; omega), getD_snoc_ne _ _ _ _ (by omega)]

theorem support_of_operand {n} (gs : List Gate) (L : List (Finset (Fin n))) (hb : Back L.length gs)
    (t : Nat) (g : Gate) (ht : gs[t]? = some g) (j : Nat) (hj : j ∈ g.inputs) :
    (suppsFrom gs L).getD j ∅ ⊆ (suppsFrom gs L).getD (L.length+t) ∅ := by
  induction gs generalizing L t with
  | nil => simp at ht
  | cons g' gs ih =>
    obtain ⟨hb, hr⟩ := hb
    let L' := L ++ [gateSupp L g']
    have len : L'.length = L.length + 1 := by simp [L']
    change (suppsFrom gs L').getD j ∅ ⊆ (suppsFrom gs L').getD (L.length+t) ∅
    cases t with
    | zero =>
      obtain rfl : g' = g := by simpa using ht
      have hj' := hb j hj
      rw [Nat.add_zero, support_old _ _ _ (by rw [len]; omega), support_old _ _ _ (by rw [len]; omega)]
      change (L ++ [_]).getD j ∅ ⊆ (L ++ [gateSupp L g']).getD L.length ∅
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_eq]
      exact fun u hu => (mem_gateSupp L g' u).mpr ⟨j,hj,hu⟩
    | succ t =>
      have := ih L' (len ▸ hr) t (by simpa using ht)
      simpa only [len, Nat.add_assoc, Nat.add_comm 1 t] using this

private theorem closed_iff (k : Nat → Bool) (gs : List Gate) (i : Nat) :
    Closed k i gs ↔ ∀ t g, gs[t]? = some g → k (i+t) = true → ∀ j ∈ g.inputs, k j = true := by
  induction gs generalizing i with
  | nil => simp [Closed]
  | cons a gs ih =>
    constructor
    · rintro ⟨ha, hr⟩ (_ | t) g he
      · obtain rfl : a = g := by simpa using he
        simpa using ha
      · have := (ih (i+1)).mp hr t g (by simpa using he)
        simpa [Nat.add_assoc, Nat.add_comm 1 t] using this
    · intro h
      refine ⟨by simpa using h 0 a (by simp), (ih (i+1)).mpr ?_⟩
      intro t g he
      simpa [Nat.add_assoc, Nat.add_comm 1 t] using h (t+1) g (by simpa using he)

namespace Fano
noncomputable def pure (C : Circuit) (w : Nat) := !(isMixed C w)

theorem pure_iff (C : Circuit) (w : Nat) : pure C w = true ↔ isPoint C w ∨ isLine C w := by
  classical
  simp only [pure, isMixed, Bool.not_eq_true', decide_eq_false_iff_not, not_and_or, not_not]

theorem pure_closed (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 14 C) : Closed (pure C) 14 C.gates := by
  apply (closed_iff ..).mpr
  intro t g ht hw j hj
  have hback := (back_iff_readsBack ..).mpr hC.2.1
  have hl : (inputSupps 14).length = 14 := by simp [inputSupps]
  have hsub := support_of_operand C.gates (inputSupps 14) (hl ▸ hback) t g ht j hj
  rw [hl] at hsub
  exact (pure_iff C j).mpr (((pure_iff C _).mp hw).imp
    (fun hp i hi => hp i (hsub hi)) (fun hline i hi => hline i (hsub hi)))

end Fano
end MixedExtract
