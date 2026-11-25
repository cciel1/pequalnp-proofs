import ThirteenReal
import PEqualNP.Outside.L_meta_4342

namespace MixedExtract.Desk582
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open FanoBoundary FanoMixedSize MixedExtract.Fano

def edges : List (Nat × Nat) :=
  [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),
   (3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]

/-- The assignment's original input numbering. -/
def deskComputes (C : Circuit) : Prop :=
  ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 14, (u.val,v.val) ∈ edges ∧ x u = true ∧ x v = true

def perm : Fin 14 → Fin 14 :=
  Fin.append (fun p : Fin 7 => Fin.castAdd 7 p) (fun l : Fin 7 => Fin.natAdd 7 (-l))

private theorem flags : ∀ u v : Fin 14, (u.val,v.val) ∈ edges ↔
    ∃ p l : Fin 7, u = Fin.castAdd 7 p ∧ v = Fin.natAdd 7 (-l) ∧ incident p l := by
  unfold edges FanoMixedSize.incident
  decide +kernel

private theorem point_perm (p : Fin 7) : perm (Fin.castAdd 7 p) = Fin.castAdd 7 p :=
  Fin.append_left _ _ _
private theorem line_perm (l : Fin 7) : perm (Fin.natAdd 7 (-l)) = Fin.natAdd 7 l := by
  unfold perm
  rw [Fin.append_right, neg_neg]

theorem renumber_computes (C : Circuit) (hc : deskComputes C) :
    ComputesFano (PermInputs.relabel 14 14 perm C) := by
  intro x y
  let z := Fin.append x y
  have he := (PermInputs.rel_fold 14 14 perm C.gates _ _
    (PermInputs.rel_init 14 14 perm z)).2.2 C.output
  change (PermInputs.relabel 14 14 perm C).eval (List.ofFn z) = true ↔ _
  rw [show (PermInputs.relabel 14 14 perm C).eval (List.ofFn z) = C.eval (List.ofFn (z ∘ perm)) from he,
    hc]
  constructor
  · rintro ⟨u,v,hf,hx,hy⟩
    obtain ⟨p,l,rfl,rfl,inc⟩ := (flags u v).mp hf
    exact ⟨p,l,inc,by simpa only [Function.comp_apply,point_perm,z,Fin.append_left] using hx,
      by simpa only [Function.comp_apply,line_perm,z,Fin.append_right] using hy⟩
  · rintro ⟨p,l,inc,hx,hy⟩
    exact ⟨Fin.castAdd 7 p,Fin.natAdd 7 (-l),(flags ..).mpr ⟨p,l,rfl,rfl,inc⟩,
      by simpa only [Function.comp_apply,point_perm,z,Fin.append_left] using hx,
      by simpa only [Function.comp_apply,line_perm,z,Fin.append_right] using hy⟩

/-- An official size-26 witness, in the relaxed Monotone2 model and original 21-edge
numbering, would yield an actual AO2 circuit with at least fourteen mixed and at most
twelve pure gates. -/
theorem normalized_witness (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 26)
    (hc : deskComputes C) : ∃ D : Circuit,
    PEqualNP.TopForm.IsAO2 14 D ∧ D.size ≤ C.size ∧ ComputesFano D ∧
    14 ≤ countFrom (isMixed D) 14 D.gates ∧ (pureCircuit D).size ≤ 12 := by
  let R := PermInputs.relabel 14 14 perm C
  have rm : Monotone2 R := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact ⟨(hm g' hg').1, by simpa [PermInputs.relGate] using (hm g' hg').2⟩
  have rsize : R.size = C.size := by simp [R, PermInputs.relabel, Circuit.size]
  have rcomp := renumber_computes C hc
  have rz : circuitFun 14 R (fun _ => false) = false := by
    have eqz : (fun _ : Fin 14 => false) = Fin.append (zero : Shore) (zero : Shore) := by
      funext i
      refine Fin.addCases (m := 7) (n := 7)
        (motive := fun j => false = Fin.append (zero : Shore) (zero : Shore) j)
        (fun _ => ?_) (fun _ => ?_) i
      · simp only [Fin.append_left, zero]
      · simp only [Fin.append_right, zero]
    rw [eqz]
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨_,_,_,hp,_⟩ := (rcomp (zero : Shore) (zero : Shore)).mp h
    contradiction
  obtain ⟨D, ha, hsize, heq⟩ := PEqualNP.Outside.L_meta_4342 14 R rm rz
  have dcomp : ComputesFano D := by
    intro x y
    change circuitFun 14 D (Fin.append x y) = true ↔ _
    rw [heq]
    exact rcomp x y
  have hle : D.size ≤ C.size := hsize.trans_eq rsize
  have h14 := mixed_ge_14_of_size_le_26 D ha dcomp (hle.trans hs)
  have hsum := size_partition D
  exact ⟨D,ha,hle,dcomp,h14,by omega⟩

#print axioms normalized_witness
end MixedExtract.Desk582
