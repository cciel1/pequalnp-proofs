import ThirteenReal

namespace MixedExtract.Fano
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open FanoBoundary FanoMixedSize

theorem port_budget (C : Circuit) (ha : PEqualNP.TopForm.IsAO2 14 C) :
    countP C + countL C ≤ countFrom (isMixed C) 14 C.gates + 1 := by
  have hcut := isAO2_extract C 14 (width C) (isMixed C) id ha
    (fun j h => by simp [width]; omega) (fun j _ h _ => h)
  have hok : ∀ g ∈ (cut C).gates, Ok g := fun g h =>
    ⟨(hcut.1 g h).imp_right Or.inl, Nat.le_of_eq (hcut.2.2 g h)⟩
  have hc := cnt_suppsFrom (cut C).gates 0 (inputSupps (width C)) hok cnt_inputs {(cut C).output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  change (live C).card ≤ (cut C).size + 1 at hc
  have hd : Disjoint (pPorts C) (lPorts C) := Finset.disjoint_left.mpr fun _ hp hl =>
    (Finset.mem_filter.mp hl).2.1 (Finset.mem_filter.mp hp).2
  have hs : pPorts C ∪ lPorts C ⊆ live C := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h <;> exact (Finset.mem_filter.mp h).1
  change (pPorts C).card + (lPorts C).card ≤ _
  rw [← Finset.card_union_of_disjoint hd]
  exact (Finset.card_le_card hs).trans (hc.trans_eq (congrArg (·+1) (size_extract ..)))

private theorem saturated_ports {a b : Nat} (C : Circuit) (hm : Monotone2 C)
    (P : Fin a → Input (Fin 7) → Bool) (L : Fin b → Input (Fin 7) → Bool)
    (hp : ∀ i, MonotoneFeature (P i)) (hl : ∀ i, MonotoneFeature (L i))
    (comp : ∀ x y, FanoMixedSize.mixed C (fun i => P i x) (fun j => L j y) = true ↔
      AcceptsEdge incident x y) (ha : a = 7) (hb : b = 7) (hsize : C.size < 20) :
    (∀ l, ∃ i : Fin a, ∀ x, P i x = true ↔ ∃ p, incident p l ∧ x p = true) ∨
    (∀ p, ∃ j : Fin b, ∀ y, L j y = true ↔ ∃ l, incident p l ∧ y l = true) := by
  subst a
  subst b
  apply seven_each_forces_exact_ors P L hp hl (FanoMixedSize.mixed C) (mixed_mono C hm) comp _ hsize
  refine ⟨C, fun g h => ⟨((hm g h).1).imp_right Or.inl, (hm g h).2⟩, le_rfl, ?_⟩
  intro z
  have eqn : z = Fin.append (m := 7) (n := 7) (z ∘ Fin.castAdd 7) (z ∘ Fin.natAdd 7) := by
    funext i
    refine Fin.addCases (m := 7) (n := 7)
      (motive := fun j => z j = (Fin.append (m := 7) (n := 7) (z ∘ Fin.castAdd 7) (z ∘ Fin.natAdd 7)) j)
      (fun _ => ?_) (fun _ => ?_) i
    · simp only [Fin.append_left, Function.comp_apply]
    · simp only [Fin.append_right, Function.comp_apply]
  exact congrArg (fun f => C.eval (List.ofFn f)) eqn

theorem more_than_fourteen_ports (C : Circuit) (ha : PEqualNP.TopForm.IsAO2 14 C)
    (hc : ComputesFano C) (hs : C.size ≤ 26) (hsmall : countFrom (isMixed C) 14 C.gates < 20) :
    15 ≤ countP C + countL C := by
  by_contra! h
  obtain ⟨hpa,hla⟩ := physical_ports_each C ha hc
  have hp7 : countP C = 7 := by omega
  have hl7 : countL C = 7 := by omega
  let z : Fin (countP C + countL C) := ⟨0, used_ports_positive C ha hc⟩
  have hor := saturated_ports (compact C z) (compact_mono C z ha) (P C) (L C)
    (fun i => point_mono C ha.1 _) (fun j => line_mono C ha.1 _)
    (fun x y => (compact_factor C z ha (output_in_range C hc) x y) ▸ hc x y)
    hp7 hl7 ((compact_size C z).trans_lt hsmall)
  have hpure := fourteen_pure C ha hor
  have hmix := thirteen_mixed C ha hc
  have add := size_partition C
  omega

theorem fourteen_port_counts (C : Circuit) (ha : PEqualNP.TopForm.IsAO2 14 C)
    (hc : ComputesFano C) (hs : C.size ≤ 26) (hm : countFrom (isMixed C) 14 C.gates = 14) :
    (countP C = 7 ∧ countL C = 8) ∨ (countP C = 8 ∧ countL C = 7) := by
  obtain ⟨hp,hl⟩ := physical_ports_each C ha hc
  have low := more_than_fourteen_ports C ha hc hs (by omega)
  have up := port_budget C ha
  omega

#print axioms port_budget
#print axioms fourteen_port_counts
end MixedExtract.Fano
