import Closed
import PureTriples

namespace MixedExtract.Fano
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity FanoBoundary FanoMixedSize

/-- Identify the point inputs with themselves and the line inputs with their additive
inverses. This lets the same seven-input circuit witness the dual family of ORs. -/
def rawMap : Fin 14 → Fin 7 := Fin.append (fun i : Fin 7 => i) (fun i : Fin 7 => -i)
def index (j : Nat) := if hj : j < 14 then (rawMap ⟨j,hj⟩).val else 0

theorem index_lt (j : Nat) : index j < 7 := by
  unfold index
  split
  · exact Fin.isLt _
  · decide

noncomputable def pureCircuit (C : Circuit) := extract C 14 7 (pure C) index
noncomputable def pureIndex (C : Circuit) := (compile (pure C) index 14 7 index C.gates).2

theorem pure_ao (C : Circuit) (ha : PEqualNP.TopForm.IsAO2 14 C) :
    PEqualNP.TopForm.IsAO2 7 (pureCircuit C) :=
  isAO2_extract C 14 7 (pure C) index ha (fun j _ => index_lt j) (fun j _ _ _ => index_lt j)

theorem size_partition (C : Circuit) :
    (pureCircuit C).size + countFrom (isMixed C) 14 C.gates = C.size := by
  change (extract C 14 7 _ _).size + _ = _
  rw [size_extract]
  have eqn (gs : List Gate) (i : Nat) :
      countFrom (pure C) i gs + countFrom (isMixed C) i gs = gs.length := by
    induction gs generalizing i with
    | nil => rfl
    | cons g gs ih =>
      have := ih (i+1)
      cases h : isMixed C i <;> simp only [countFrom, pure, h, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, ite_true, ite_false, List.length_cons] <;> omega
  exact eqn C.gates 14

private theorem raw_eq (x : Shore) : x ∘ rawMap = Fin.append x (fun i : Fin 7 => x (-i)) := by
  funext i
  refine Fin.addCases (m := 7) (n := 7)
    (motive := fun j => (x ∘ rawMap) j = (Fin.append x (fun j : Fin 7 => x (-j))) j)
    (fun j => ?_) (fun j => ?_) i
  · simp only [Function.comp_apply, rawMap, Fin.append_left]
  · simp only [Function.comp_apply, rawMap, Fin.append_right]

theorem pure_wire (C : Circuit) (ha : PEqualNP.TopForm.IsAO2 14 C) (x : Shore)
    (w : Fin (width C)) (hp : pure C w = true) :
    wire (pureCircuit C) x (pureIndex C w) = wire C (Fin.append x (fun i => x (-i))) w := by
  rw [← raw_eq]
  let raw := List.ofFn (x ∘ rawMap)
  let b := List.ofFn x
  have hraw : raw.length = 14 := by simp [raw]
  have hb : b.length = 7 := by simp [b]
  have hm : MapsKept (pure C) raw b index := by
    intro j hj _
    have hj' : j < 14 := by omega
    have hj7 : index j < b.length := by rw [hb]; exact index_lt j
    refine ⟨hj7, ?_⟩
    rw [List.getD_eq_getElem _ _ hj7, List.getD_eq_getElem _ _ hj]
    simp only [raw, b, List.getElem_ofFn, index, dite_eq_left hj', Function.comp_apply]
  have rel := simulate_closed (pure C) index C.gates raw b index hm
    (hraw ▸ (back_iff_readsBack ..).mpr ha.2.1) (hraw ▸ pure_closed C ha)
  have hw : w.val < (C.gates.foldl step raw).length := by
    rw [show (C.gates.foldl step raw).length = raw.length + C.gates.length from
      LineDegTest.W_length C.gates raw, hraw]
    exact w.isLt
  have hv := (rel w hw hp).2
  change ((compile (pure C) index 14 7 index C.gates).1.foldl step b).getD
    ((compile (pure C) index 14 7 index C.gates).2 w) false =
    (C.gates.foldl step raw).getD w false
  simpa only [hraw, hb] using hv

private noncomputable def pointWire (C : Circuit) (i : Fin (countP C)) : Fin (width C) :=
  ((pPorts C).equivFin.symm i).val
private noncomputable def lineWire (C : Circuit) (i : Fin (countL C)) : Fin (width C) :=
  ((lPorts C).equivFin.symm i).val

theorem pure_points (C : Circuit) (ha : PEqualNP.TopForm.IsAO2 14 C) (i : Fin (countP C)) (x : Shore) :
    wire (pureCircuit C) x (pureIndex C (pointWire C i)) = P C i x := by
  have hp : isPoint C (pointWire C i) := (Finset.mem_filter.mp ((pPorts C).equivFin.symm i).property).2
  exact (pure_wire C ha x _ ((pure_iff ..).mpr (Or.inl hp))).trans
    (point_factor C _ hp x (fun j => x (-j))).symm

theorem pure_lines (C : Circuit) (ha : PEqualNP.TopForm.IsAO2 14 C) (i : Fin (countL C)) (x : Shore) :
    wire (pureCircuit C) x (pureIndex C (lineWire C i)) = L C i (fun j => x (-j)) := by
  have hl : isLine C (lineWire C i) := (Finset.mem_filter.mp ((lPorts C).equivFin.symm i).property).2.2
  exact (pure_wire C ha x _ ((pure_iff ..).mpr (Or.inr hl))).trans
    (line_factor C _ hl x (fun j => x (-j))).symm

private theorem flip_incidence : ∀ p l : Fin 7, incident p l ↔ incident (-l) (-p) := by unfold FanoMixedSize.incident; decide

/-- Seven exact neighborhoods on either shore require fourteen of the original
circuit's pure gates. The seven-input witness consists only of the retained pure gates. -/
theorem fourteen_pure (C : Circuit) (ha : PEqualNP.TopForm.IsAO2 14 C)
    (hor : (∀ l, ∃ i : Fin (countP C), ∀ x, P C i x = true ↔ ∃ p, incident p l ∧ x p = true) ∨
           (∀ p, ∃ i : Fin (countL C), ∀ y, L C i y = true ↔ ∃ l, incident p l ∧ y l = true)) :
    14 ≤ (pureCircuit C).size := by
  classical
  rcases hor with h | h
  · choose idx hi using h
    apply FanoPureTriples.exact_floor (pure_ao C ha) (fun l => pureIndex C (pointWire C (idx l)))
    intro l x
    change wire (pureCircuit C) x _ = true ↔ _
    rw [pure_points C ha (idx l) x]
    exact hi l x
  · choose idx hi using h
    apply FanoPureTriples.exact_floor (pure_ao C ha) (fun l => pureIndex C (lineWire C (idx (-l))))
    intro l x
    change wire (pureCircuit C) x _ = true ↔ _
    rw [pure_lines C ha (idx (-l)) x, hi]
    constructor
    · rintro ⟨q,hq,hx⟩
      exact ⟨-q, by change incident (-q) l; simpa only [neg_neg] using (flip_incidence (-l) q).mp hq, hx⟩
    · rintro ⟨q,hq,hx⟩
      exact ⟨-q, (flip_incidence q l).mp hq, by simpa only [neg_neg] using hx⟩

#print axioms pure_wire
#print axioms fourteen_pure
end MixedExtract.Fano
