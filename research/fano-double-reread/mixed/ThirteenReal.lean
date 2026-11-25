import Application
import Pure
import Thirteen
import AtMostOne

namespace MixedExtract.Fano
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity FanoBoundary FanoMixedSize

/-- At most thirteen genuinely mixed gates require the pure subcircuit to have
fourteen gates and the entire AO2 circuit to have at least twenty-seven gates. -/
theorem size_ge_27_of_mixed_le_13 (C : Circuit) (ha : PEqualNP.TopForm.IsAO2 14 C)
    (hc : ComputesFano C) (hm : countFrom (isMixed C) 14 C.gates ≤ 13) :
    14 ≤ (pureCircuit C).size ∧ 27 ≤ C.size := by
  let z : Fin (countP C + countL C) := ⟨0, used_ports_positive C ha hc⟩
  have budget : (compact C z).size ≤ 13 := (compact_size C z).trans_le hm
  have hor := thirteen_forces_exact_ors (compact C z) (compact_mono C z ha) budget
    (P C) (L C) (fun i => point_mono C ha.1 _) (fun j => line_mono C ha.1 _)
    (fun x y => (compact_factor C z ha (output_in_range C hc) x y) ▸ hc x y)
  have h14 := fourteen_pure C ha hor
  have h13 := thirteen_mixed C ha hc
  have hsum := size_partition C
  exact ⟨h14, by omega⟩

/-- Any proposed size-26 circuit must have at least fourteen mixed gates, even
with arbitrary monotone pure preprocessing. -/
theorem mixed_ge_14_of_size_le_26 (C : Circuit) (ha : PEqualNP.TopForm.IsAO2 14 C)
    (hc : ComputesFano C) (hsize : C.size ≤ 26) : 14 ≤ countFrom (isMixed C) 14 C.gates := by
  by_contra! h
  have := (size_ge_27_of_mixed_le_13 C ha hc (by omega)).2
  omega

/-- If every actually reachable pure port accepts at most one raw singleton on its
own shore, the original circuit has at least twenty genuinely two-shore gates. -/
theorem twenty_mixed (C : Circuit) (ha : PEqualNP.TopForm.IsAO2 14 C) (hc : ComputesFano C)
    (p : Fin (countP C) → Option (Fin 7)) (l : Fin (countL C) → Option (Fin 7))
    (hp : ∀ i v, P C i (one v) = true ↔ p i = some v)
    (hl : ∀ i v, L C i (one v) = true ↔ l i = some v) :
    20 ≤ countFrom (isMixed C) 14 C.gates := by
  let z : Fin (countP C + countL C) := ⟨0, used_ports_positive C ha hc⟩
  rw [← compact_size C z]
  apply at_most_one_mixed_floor _ (compact_mono C z ha) (P C) (L C)
    (fun i => point_mono C ha.1 _) (fun j => line_mono C ha.1 _) p l hp hl
  intro x y
  rw [compact_factor C z ha (output_in_range C hc)]
  exact hc x y



#print axioms size_ge_27_of_mixed_le_13
#print axioms mixed_ge_14_of_size_le_26
#print axioms twenty_mixed
end MixedExtract.Fano
