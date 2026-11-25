import PEqualNP.Outside.L_meta_2225
import PEqualNP.Outside.L_meta_2227

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

namespace FanoPruning

-- The derivative conditions alone suffice, for either choice of first gate.
-- The list counts only internal wires, across all gate inputs and the designated output.
theorem internalWireMustRepeatOfDoubleRead :
    ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
      (∀ j < C.size, opnd C j 0 ≠ opnd C j 1) →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
          x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) →
      (∀ s : Bool, ∃ v : ℕ → Bool,
        let W := C.wires (List.ofFn (fun i : Fin 14 =>
          decide (i = if s then 0 else 7)))
        (∀ i < 14, v i = decide (i = if s then 7 else 0)) ∧
        (∀ j < C.size,
          let g := gateAt C j
          let a := opnd C j 0
          let b := opnd C j 1
          (g.op = .and →
            v (14 + j) = ((W.getD a false && v b) || (v a && W.getD b false))) ∧
          (g.op = .or → v (14 + j) = (v a || v b))) ∧ v C.output = false) →
      ¬ ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))).Nodup := by
  intro C hsize hm distinct correct reads tree
  have hget (C : Circuit) (j : ℕ) (hj : j < C.size) : C.gates[j]? = some (gateAt C j) := by
    change C.gates[j]? = some (C.gates.getD j ⟨.or, []⟩)
    rw [List.getElem?_eq_getElem (show j < C.gates.length from hj),
      List.getD_eq_getElem _ _ (show j < C.gates.length from hj)]
  have hopnd (C : Circuit) (j a b : ℕ) (hab : (gateAt C j).inputs = [a, b]) :
      opnd C j 0 = a ∧ opnd C j 1 = b := by
    change (gateAt C j).inputs.getD 0 0 = a ∧ (gateAt C j).inputs.getD 1 0 = b
    rw [hab]
    exact ⟨rfl, rfl⟩
  have hg (j : ℕ) (g : Gate) (he : C.gates[j]? = some g) :
      (g.op = .and ∨ g.op = .or) ∧ ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j := by
    have hj : j < C.size := by
      change j < C.gates.length
      exact List.getElem?_eq_some_iff.mp he |>.choose
    have mem := List.mem_of_getElem? he
    have len := hm.2.2 g mem
    obtain ⟨a,b,hab⟩ : ∃ a b, g.inputs = [a,b] := List.length_eq_two.mp len
    have eqg := Option.some.inj ((hget C j hj).symm.trans he)
    obtain ⟨ha,hb⟩ := hopnd C j a b (eqg ▸ hab)
    refine ⟨hm.1 g mem,a,b,hab,?_,?_,?_⟩
    · simpa [ha,hb] using distinct j hj
    · apply hm.2.1 j hj a
      simp [eqg,hab]
    · apply hm.2.1 j hj b
      simp [eqg,hab]
  let one (i j : Fin 14) : Bool := decide (j = i)
  have off (i : Fin 14) : C.eval (List.ofFn (one i)) = false := by
    cases h : C.eval (List.ofFn (one i)) with
    | false => rfl
    | true =>
      obtain ⟨u, t, _, hu, ht⟩ := (correct _).mp h
      have eq := (of_decide_eq_true hu).trans (of_decide_eq_true ht).symm
      have disjoint : ∀ u t : Fin 7, Fin.castAdd 7 u ≠ Fin.natAdd 7 t := by decide
      exact False.elim (disjoint u t eq)
  have degree (s : Bool) :
      2 ≤ C.lineDeg 14 {(if s then (7 : Fin 14) else 0).val} := by
    let i : Fin 14 := if s then 7 else 0
    let k : Fin 14 := if s then 0 else 7
    obtain ⟨v, vi, vg, vo⟩ := reads s
    apply PEqualNP.Outside.L_meta_2227 C i (one k) v hg
    · intro j
      rw [vi j.val j.isLt]
      apply decide_eq_decide.mpr
      rw [Fin.ext_iff]
      cases s <;> exact eq_comm
    · intro j g a b he hab
      have hj : j < C.size := (List.getElem?_eq_some_iff.mp he).choose
      have eqg := Option.some.inj ((hget C j hj).symm.trans he)
      obtain ⟨ha, hb⟩ := hopnd C j a b (eqg ▸ hab)
      simpa only [eqg, ha, hb, k, one] using vg j hj
    · exact off k
    · apply (correct _).mpr
      refine ⟨0, 0, Or.inl rfl, ?_, ?_⟩ <;> cases s <;> decide
    · exact vo
  rcases PEqualNP.Outside.L_meta_2225 C 0 0 ⟨hsize, hg, correct⟩ tree (Or.inl rfl) with h | h
  · change C.lineDeg 14 {0} ≤ 1 at h
    have lo : 2 ≤ C.lineDeg 14 {0} := degree false
    omega
  · change C.lineDeg 14 {7} ≤ 1 at h
    have lo : 2 ≤ C.lineDeg 14 {7} := degree true
    omega

theorem internalWireMustRepeat :
    ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
      (∀ j < C.size, opnd C j 0 ≠ opnd C j 1) →
      (gateAt C 0).op = .or →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
          x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) →
      (∀ s : Bool, ∃ v : ℕ → Bool,
        let W := C.wires (List.ofFn (fun i : Fin 14 =>
          decide (i = if s then 0 else 7)))
        (∀ i < 14, v i = decide (i = if s then 7 else 0)) ∧
        (∀ j < C.size,
          let g := gateAt C j
          let a := opnd C j 0
          let b := opnd C j 1
          (g.op = .and →
            v (14 + j) = ((W.getD a false && v b) || (v a && W.getD b false))) ∧
          (g.op = .or → v (14 + j) = (v a || v b))) ∧ v C.output = false) →
      ¬ ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))).Nodup := by
  intro C hsize hm distinct _first
  exact internalWireMustRepeatOfDoubleRead C hsize hm distinct

-- Exact printed hypotheses of L-meta-2348, with only its conclusion weakened.
example :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.or →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (∀ (x7 : Bool),                 ∃ (x8 : ℕ → Bool),                   have x9 : List Bool := x1.wires (List.ofFn fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = if x7 = Bool.true then (0 : Fin (14 : ℕ)) else (7 : Fin (14 : ℕ))));                   (∀ x10 < (14 : ℕ), x8 x10 = Decidable.decide (x10 = if x7 = Bool.true then (7 : ℕ) else (0 : ℕ))) ∧                     (∀ x10 < x1.size,                         have x12 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10;                         have x13 : ℕ := PEqualNP.TopForm.opnd x1 x10 (0 : Fin (2 : ℕ));                         have x14 : ℕ := PEqualNP.TopForm.opnd x1 x10 (1 : Fin (2 : ℕ));                         (x12.op = PEqualNP.CircuitLowerBounds.GateOp.and → x8 ((14 : ℕ) + x10) = (x9.getD x13 Bool.false && x8 x14 || x8 x13 && x9.getD x14 Bool.false)) ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or → x8 ((14 : ℕ) + x10) = (x8 x13 || x8 x14))) ∧                       x8 x1.output = Bool.false) →               ¬ ((x1.output :: x1.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))).Nodup :=
  internalWireMustRepeat

end FanoPruning

#print axioms FanoPruning.internalWireMustRepeat
