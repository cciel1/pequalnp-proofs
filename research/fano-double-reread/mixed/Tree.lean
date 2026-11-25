import FourteenReal

namespace MixedExtract.Tree
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers

/-- Backward demand from required output wires. At gate wire i, replace its demand
with its two operands only if a later gate or the output needs it. -/
def expand (i : Nat) (g : Gate) (need : Finset Nat) :=
  if i ∈ need then need.erase i ∪ g.inputs.toFinset else need
def frontier (i : Nat) (gs : List Gate) (need : Finset Nat) : Finset Nat :=
  match gs with
  | [] => need
  | g :: tail => expand i g (frontier (i+1) tail need)

/-- Every gate is used, it reads two distinct wires, and neither operand already
has a pending use. These are the equalities in the connected binary-DAG input bound. -/
def readOnce (i : Nat) (gs : List Gate) (need : Finset Nat) : Prop :=
  match gs with
  | [] => True
  | g :: tail =>
    let later := frontier (i+1) tail need
    i ∈ later ∧ g.inputs.toFinset.card = 2 ∧
      Disjoint (later.erase i) g.inputs.toFinset ∧ readOnce (i+1) tail need

private theorem expand_le (i : Nat) (g : Gate) (need : Finset Nat) (hb : g.inputs.length ≤ 2) :
    (expand i g need).card ≤ need.card + 1 := by
  unfold expand
  split
  · rename_i hi
    have hneq := Finset.card_pos.mpr ⟨i,hi⟩
    have h := Finset.card_union_le (need.erase i) g.inputs.toFinset
    rw [Finset.card_erase_of_mem hi] at h
    have := List.toFinset_card_le g.inputs
    omega
  · omega

private theorem expand_eq (i : Nat) (g : Gate) (need : Finset Nat) (hb : g.inputs.length ≤ 2)
    (heq : (expand i g need).card = need.card+1) :
    i ∈ need ∧ g.inputs.toFinset.card = 2 ∧ Disjoint (need.erase i) g.inputs.toFinset := by
  by_cases hi : i ∈ need
  · have pos := Finset.card_pos.mpr ⟨i,hi⟩
    rw [expand, ite_eq_left hi] at heq
    have hu := Finset.card_union_le (need.erase i) g.inputs.toFinset
    have hg := List.toFinset_card_le g.inputs
    have era := Finset.card_erase_of_mem hi
    refine ⟨hi, by omega, Finset.card_union_eq_card_add_card.mp ?_⟩
    omega
  · simp [expand, hi] at heq

theorem frontier_le (gs : List Gate) (i : Nat) (need : Finset Nat)
    (hb : ∀ g ∈ gs, g.inputs.length ≤ 2) : (frontier i gs need).card ≤ need.card + gs.length := by
  induction gs generalizing i with
  | nil => simp [frontier]
  | cons g tail ih =>
    have h1 := ih (i+1) (fun a ha => hb a (List.mem_cons_of_mem g ha))
    have h2 := expand_le i g (frontier (i+1) tail need) (hb g (by simp))
    simpa only [frontier, List.length_cons] using (show _ ≤ need.card + (tail.length+1) by omega)

theorem readOnce_of_tight (gs : List Gate) (i : Nat) (need : Finset Nat)
    (hb : ∀ g ∈ gs, g.inputs.length ≤ 2) (he : (frontier i gs need).card = need.card + gs.length) :
    readOnce i gs need := by
  induction gs generalizing i with
  | nil => trivial
  | cons g tail ih =>
    have ht : ∀ a ∈ tail, a.inputs.length ≤ 2 := fun a ha => hb a (List.mem_cons_of_mem g ha)
    have h1 := frontier_le tail (i+1) need ht
    have h2 := expand_le i g (frontier (i+1) tail need) (hb g (by simp))
    change (expand i g (frontier (i+1) tail need)).card = _ at he
    rw [List.length_cons] at he
    obtain ⟨hi,hg,hd⟩ := expand_eq i g (frontier (i+1) tail need) (hb g (by simp)) (by omega)
    exact ⟨hi,hg,hd,ih (i+1) ht (by omega)⟩

private theorem support_expand {n : Nat} (W : List (Finset (Fin n))) (g : Gate) (need : Finset Nat) :
    need.biUnion (fun j => (W ++ [gateSupp W g]).getD j ∅) =
    (expand W.length g need).biUnion (fun j => W.getD j ∅) := by
  classical
  ext p
  simp only [Finset.mem_biUnion]
  by_cases hc : W.length ∈ need
  · rw [expand, ite_eq_left hc]
    constructor
    · rintro ⟨j,hj,hp⟩
      by_cases he : j = W.length
      · subst j
        rw [getD_snoc_eq] at hp
        obtain ⟨a,ha,h⟩ := (mem_gateSupp W g p).mp hp
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.mpr ha), h⟩
      · rw [getD_snoc_ne _ _ _ _ he] at hp
        exact ⟨j,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he,hj⟩),hp⟩
    · rintro ⟨j,hj,hp⟩
      rcases Finset.mem_union.mp hj with hj | hj
      · obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hj
        exact ⟨j,hm,by rwa [getD_snoc_ne _ _ _ _ hne]⟩
      · refine ⟨W.length,hc,?_⟩
        rw [getD_snoc_eq]
        exact (mem_gateSupp W g p).mpr ⟨j,List.mem_toFinset.mp hj,hp⟩
  · rw [expand, ite_eq_right hc]
    constructor <;> rintro ⟨j,hj,hp⟩ <;>
      have he : j ≠ W.length := fun e => hc (e ▸ hj)
    · exact ⟨j,hj, by rwa [getD_snoc_ne _ _ _ _ he] at hp⟩
    · exact ⟨j,hj, by rwa [getD_snoc_ne _ _ _ _ he]⟩

theorem support_frontier {n} (gs : List Gate) (W : List (Finset (Fin n))) (need : Finset Nat) :
    need.biUnion (fun j => (suppsFrom gs W).getD j ∅) =
    (frontier W.length gs need).biUnion (fun j => W.getD j ∅) := by
  induction gs generalizing W with
  | nil => rfl
  | cons g tail ih =>
    let W' := W ++ [gateSupp W g]
    change need.biUnion (fun j => (suppsFrom tail W').getD j ∅) = _
    rw [ih W']
    have hl : W'.length = W.length + 1 := by simp [W']
    rw [hl]
    exact support_expand W g (frontier (W.length+1) tail need)

theorem frontier_covers (n : Nat) (C : Circuit) :
    (Fano.support n C C.output).card ≤ (frontier n C.gates {C.output}).card := by
  have he := support_frontier C.gates (inputSupps n) {C.output}
  simp only [Finset.singleton_biUnion] at he
  have hl : (inputSupps n).length = n := by simp [inputSupps]
  rw [hl] at he
  change ((suppsFrom C.gates (inputSupps n)).getD C.output ∅).card ≤ _
  rw [he]
  simpa only [zero_add] using (cnt_inputs (n := n) (frontier n C.gates {C.output}))

/-- In a candidate of size 26 with exactly fourteen mixed gates, the mixed core
must be a read-once binary tree on fifteen different actual inputs. -/
theorem fourteen_is_tree (C : Circuit) (ha : PEqualNP.TopForm.IsAO2 14 C)
    (hc : Fano.ComputesFano C) (hs : C.size ≤ 26)
    (hm : countFrom (Fano.isMixed C) 14 C.gates = 14) :
    readOnce (Fano.width C) (Fano.cut C).gates {(Fano.cut C).output} ∧
    (frontier (Fano.width C) (Fano.cut C).gates {(Fano.cut C).output}).card = 15 := by
  have hcut := isAO2_extract C 14 (Fano.width C) (Fano.isMixed C) id ha
    (fun j h => by simp [Fano.width]; omega) (fun j _ h _ => h)
  have hg : ∀ g ∈ (Fano.cut C).gates, g.inputs.length ≤ 2 := fun g h => Nat.le_of_eq (hcut.2.2 g h)
  have hd : Disjoint (Fano.pPorts C) (Fano.lPorts C) := Finset.disjoint_left.mpr fun _ hp hl =>
    (Finset.mem_filter.mp hl).2.1 (Finset.mem_filter.mp hp).2
  have hsub : Fano.pPorts C ∪ Fano.lPorts C ⊆ Fano.live C := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h <;> exact (Finset.mem_filter.mp h).1
  have hnum := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd] at hnum
  change Fano.countP C + Fano.countL C ≤ (Fano.live C).card at hnum
  have hmin := Fano.more_than_fourteen_ports C ha hc hs (by omega)
  have hcovers := frontier_covers (Fano.width C) (Fano.cut C)
  change (Fano.live C).card ≤ _ at hcovers
  have hmax := frontier_le (Fano.cut C).gates (Fano.width C) {(Fano.cut C).output} hg
  simp only [Finset.card_singleton] at hmax
  have hsize : (Fano.cut C).gates.length = 14 := (size_extract C 14 _ _ _).trans hm
  constructor
  · apply readOnce_of_tight _ _ _ hg
    simp only [Finset.card_singleton]
    omega
  · omega

#print axioms fourteen_is_tree
end MixedExtract.Tree
