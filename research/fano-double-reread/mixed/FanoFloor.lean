import PEqualNP.Outside.L_meta_5670

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace FanoFloor

/-- The Fano incidence edge function using the desk's point and line coordinates. -/
def fano14 (x : Fin 14 → Bool) : Bool :=
  decide (∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
    x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)

private def pairs : List (Fin 7 × Fin 7) :=
  [(0, 0), (1, 0), (3, 0), (1, 1), (2, 1), (4, 1), (2, 2), (3, 2), (5, 2), (3, 3), (4, 3), (6, 3), (0, 4), (4, 4), (5, 4), (1, 5), (5, 5), (6, 5), (0, 6), (2, 6), (6, 6)]

set_option maxRecDepth 10000 in
private theorem pairs_spec : ∀ p l : Fin 7,
    (p = l ∨ p = l + 1 ∨ p = l + 3) ↔ (p,l) ∈ pairs := by decide

private def dnf (x : Fin 14 → Bool) : Bool :=
  (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 4 && x 8) || (x 2 && x 9) || (x 3 && x 9) || (x 5 && x 9) || (x 3 && x 10) || (x 4 && x 10) || (x 6 && x 10) || (x 0 && x 11) || (x 4 && x 11) || (x 5 && x 11) || (x 1 && x 12) || (x 5 && x 12) || (x 6 && x 12) || (x 0 && x 13) || (x 2 && x 13) || (x 6 && x 13)

private theorem fano14_eq_dnf : fano14 = dnf := by
  funext x
  have hp : fano14 x = pairs.any (fun e =>
      x (Fin.castAdd 7 e.1) && x (Fin.natAdd 7 e.2)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [fano14, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true]
    constructor
    · rintro ⟨p,l,hm,hp,hl⟩
      exact ⟨(p,l), (pairs_spec p l).mp hm, hp, hl⟩
    · rintro ⟨⟨p,l⟩,hm,hp,hl⟩
      exact ⟨p,l, (pairs_spec p l).mpr hm, hp, hl⟩
  rw [hp]
  simp only [pairs, List.any_cons, List.any_nil, Bool.or_false, dnf, Bool.or_assoc]
  rfl

/-- Even circuits allowing NOT gates, repeated, missing or unused wires, and free inputs
require at least twenty gates to compute the ordinary incidence function. -/
theorem floor {k : ℕ} (h : HasCircuitSize 14 fano14 k) : 20 ≤ k := by
  rw [fano14_eq_dnf] at h
  exact PEqualNP.Outside.L_meta_5670 k h

theorem official_floor (C : Circuit) (hC : Monotone2 C)
    (computes : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
        x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) : 20 ≤ C.size := by
  apply floor
  refine ⟨C, ?_, le_rfl, fun x => ?_⟩
  · intro g hg
    have h := hC g hg
    constructor
    · rcases h.1 with ha | ho
      · simp [ha]
      · simp [Set.mem_singleton_iff.mp ho]
    · exact h.2
  · apply Bool.eq_iff_iff.mpr
    simpa only [fano14, decide_eq_true_eq] using computes x

#print axioms floor
#print axioms official_floor
end FanoFloor
