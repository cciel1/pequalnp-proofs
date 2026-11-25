import Factor
import BothShores
import ConeBudget

namespace MixedExtract.Fano
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity FanoBoundary FanoMixedSize

/-- The output computes the actual Fano relation used by the desk, with ordinary
point and line coordinates concatenated in that order. -/
def ComputesFano (C : Circuit) : Prop :=
  ∀ x y : Shore, C.eval (List.ofFn (Fin.append x y)) = true ↔ AcceptsEdge incident x y

private theorem witnesses (C : Circuit) (hc : ComputesFano C) :
    C.eval (List.ofFn (Fin.append (one (0 : Fin 7)) (one (0 : Fin 7)))) = true ∧
    C.eval (List.ofFn (Fin.append (zero : Shore) (zero : Shore))) = false := by
  constructor
  · exact (hc _ _).mpr ⟨0,0,Or.inl rfl,by simp [one],by simp [one]⟩
  · apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨_, _, _, hx, _⟩ := (hc _ _).mp h
    contradiction

theorem output_in_range (C : Circuit) (hc : ComputesFano C) : C.output < width C := by
  by_contra! h
  have htrue := (witnesses C hc).1
  unfold Circuit.eval at htrue
  rw [List.getD_eq_default] at htrue
  · contradiction
  · rw [show ∀ (v : List Bool), (C.wires v).length = v.length + C.gates.length from
      fun v => LineDegTest.W_length C.gates v, List.length_ofFn]
    exact h

theorem used_ports_positive (C : Circuit) (ha : PEqualNP.TopForm.IsAO2 14 C) (hc : ComputesFano C) :
    0 < countP C + countL C := by
  have ⟨hon,hoff⟩ := witnesses C hc
  exact port_nonempty C ha (output_in_range C hc) (one 0) (one 0) zero zero (by rw [hon, hoff]; decide)

private noncomputable def selected (C : Circuit) (ha : PEqualNP.TopForm.IsAO2 14 C) (hc : ComputesFano C) :
    Fin (countP C + countL C) := ⟨0, used_ports_positive C ha hc⟩

theorem physical_ports_each (C : Circuit) (ha : PEqualNP.TopForm.IsAO2 14 C) (hc : ComputesFano C) :
    7 ≤ countP C ∧ 7 ≤ countL C := by
  let z := selected C ha hc
  apply seven_features_each (P C) (L C)
    (fun i => point_mono C ha.1 _) (fun j => line_mono C ha.1 _)
    (FanoMixedSize.mixed (compact C z)) (mixed_mono _ (compact_mono C z ha))
  intro x y
  rw [compact_factor C z ha (output_in_range C hc)]
  exact hc x y

theorem thirteen_mixed (C : Circuit) (ha : PEqualNP.TopForm.IsAO2 14 C) (hc : ComputesFano C) :
    13 ≤ countFrom (isMixed C) 14 C.gates := by
  let z := selected C ha hc
  rw [← compact_size C z]
  apply arbitrary_mixed_floor _ (compact_mono C z ha) (P C) (L C)
    (fun i => point_mono C ha.1 _) (fun j => line_mono C ha.1 _)
  intro x y
  rw [compact_factor C z ha (output_in_range C hc)]
  exact hc x y

#print axioms physical_ports_each
#print axioms thirteen_mixed
end MixedExtract.Fano
