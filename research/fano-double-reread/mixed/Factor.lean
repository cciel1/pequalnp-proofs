import Extract
import Compression

namespace MixedExtract.Fano
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open FanoBoundary
abbrev Shore := Fin 7 → Bool
def support (n : Nat) (C : Circuit) (w : Nat) := (supportTrace n C).getD w ∅
def wire {n : Nat} (C : Circuit) (x : Fin n → Bool) (w : Nat) :=
  (C.wires (List.ofFn x)).getD w false

theorem support_agree {n : Nat} (C : Circuit) (x y : Fin n → Bool) (w : Nat)
    (h : ∀ i ∈ support n C w, x i = y i) : wire C x w = wire C y w :=
  (agree_wiresFrom x y C.gates _ _ _ (agree_inputs x y)).2.2 w h

theorem wire_mono {n : Nat} (C : Circuit) (hC : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (w : Nat) (h : Below x y) :
    wire C x w = true → wire C y w = true := by
  apply LineDegTest.W_mono C.gates hC (List.ofFn x) (List.ofFn y) (by simp) _ w
  intro j hj
  by_cases e : j < n
  · simpa [e] using h ⟨j,e⟩ (by simpa [e] using hj)
  · simp [e] at hj

def isPoint (C : Circuit) (w : Nat) : Prop := ∀ i ∈ support 14 C w, i.val < 7
def isLine (C : Circuit) (w : Nat) : Prop := ∀ i ∈ support 14 C w, 7 ≤ i.val
noncomputable instance (C : Circuit) (w : Nat) : Decidable (isPoint C w) := Classical.propDecidable _
noncomputable instance (C : Circuit) (w : Nat) : Decidable (isLine C w) := Classical.propDecidable _
noncomputable def isMixed (C : Circuit) (w : Nat) := decide (¬isPoint C w ∧ ¬isLine C w)

def pointFeature (C : Circuit) (w : Nat) (x : Shore) :=
  wire C (Fin.append x (fun _ : Fin 7 => false)) w
def lineFeature (C : Circuit) (w : Nat) (y : Shore) :=
  wire C (Fin.append (fun _ : Fin 7 => false) y) w

theorem point_factor (C : Circuit) (w : Nat) (hw : isPoint C w) (x y : Shore) :
    pointFeature C w x = wire C (Fin.append x y) w := by
  apply support_agree
  intro i
  refine Fin.addCases (fun i _ => by simp) (fun j hj => ?_) i
  have h := hw _ hj
  simp at h

theorem line_factor (C : Circuit) (w : Nat) (hw : isLine C w) (x y : Shore) :
    lineFeature C w y = wire C (Fin.append x y) w := by
  apply support_agree
  intro i
  refine Fin.addCases (fun i hi => ?_) (fun j _ => by simp only [Fin.append_right]) i
  have h := hw _ hi
  simp at h
  omega

theorem point_mono (C : Circuit) (hC : PEqualNP.EdgeOwnership.AndOrOnly C) (w : Nat) :
    MonotoneFeature (pointFeature C w) := by
  intro x y h
  apply wire_mono C hC _ _ w
  intro i
  exact Fin.addCases (fun i => by simpa using h i) (fun i => by simp only [Fin.append_right, imp_self]) i

theorem line_mono (C : Circuit) (hC : PEqualNP.EdgeOwnership.AndOrOnly C) (w : Nat) :
    MonotoneFeature (lineFeature C w) := by
  intro x y h
  apply wire_mono C hC _ _ w
  intro i
  exact Fin.addCases (fun i => by simp) (fun i => by simpa only [Fin.append_right] using h i) i

private theorem input_supp_from {n : Nat} (gs : List Gate) (L : List (Finset (Fin n)))
    (w : Nat) (hw : w < L.length) : (suppsFrom gs L).getD w ∅ = L.getD w ∅ := by
  induction gs generalizing L with
  | nil => rfl
  | cons g gs ih =>
    change (suppsFrom gs (L ++ [gateSupp L g])).getD w ∅ = _
    rw [ih _ (by simp; omega), getD_snoc_ne _ _ _ _ (by omega)]

theorem input_pure (C : Circuit) (w : Nat) (hw : w < 14) : isPoint C w ∨ isLine C w := by
  have hs : support 14 C w = {⟨w,hw⟩} := by
    unfold support supportTrace
    rw [input_supp_from _ _ _ (by simpa [inputSupps] using hw)]
    rw [List.getD_eq_getElem _ _ (by simpa [inputSupps] using hw)]
    exact List.getElem_ofFn (f := fun i : Fin 14 => ({i} : Finset (Fin 14))) (by simpa using hw)
  by_cases h : w < 7
  · left; simpa [isPoint, hs] using h
  · right; simpa [isLine, hs] using (Nat.le_of_not_gt h)

def width (C : Circuit) := 14 + C.gates.length
noncomputable def cut (C : Circuit) := extract C 14 (width C) (isMixed C) id
noncomputable def live (C : Circuit) : Finset (Fin (width C)) :=
  support (width C) (cut C) (cut C).output
noncomputable def pPorts (C : Circuit) := (live C).filter fun (w : Fin (width C)) => isPoint C w
noncomputable def lPorts (C : Circuit) := (live C).filter fun (w : Fin (width C)) => ¬isPoint C w ∧ isLine C w
noncomputable abbrev countP (C : Circuit) := (pPorts C).card
noncomputable abbrev countL (C : Circuit) := (lPorts C).card
noncomputable def P (C : Circuit) (i : Fin (countP C)) := pointFeature C ((pPorts C).equivFin.symm i).val
noncomputable def L (C : Circuit) (i : Fin (countL C)) := lineFeature C ((lPorts C).equivFin.symm i).val

noncomputable def port (C : Circuit) (fallback : Fin (countP C + countL C)) (w : Fin (width C)) :=
  if hp : w ∈ pPorts C then Fin.castAdd (countL C) ((pPorts C).equivFin ⟨w,hp⟩)
  else if hl : w ∈ lPorts C then Fin.natAdd (countP C) ((lPorts C).equivFin ⟨w,hl⟩)
  else fallback

noncomputable def compact (C : Circuit) (z : Fin (countP C+countL C)) :=
  PermInputs.relabel (width C) (countP C+countL C) (port C z) (cut C)

theorem compact_size (C : Circuit) (z) :
    (compact C z).size = countFrom (isMixed C) 14 C.gates := by
  simpa [compact, PermInputs.relabel, Circuit.size, cut] using size_extract C 14 (width C) (isMixed C) id

theorem compact_mono (C : Circuit) (z) (hC : PEqualNP.TopForm.IsAO2 14 C) :
    Monotone2 (compact C z) := by
  have hc := isAO2_extract C 14 (width C) (isMixed C) id hC
    (fun j h => by simp [width]; omega) (fun j _ h _ => h)
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  exact ⟨hc.1 g' hg', by simp [PermInputs.relGate, hc.2.2 _ hg']⟩

private theorem input_wire {n : Nat} (C : Circuit) (x : Fin n → Bool) (w : Nat)
    (hw : w < n) : wire C x w = (List.ofFn x).getD w false := by
  let ws := List.ofFn x
  have H (gs : List Gate) (u : List Bool) (h : w < u.length) :
      (gs.foldl step u).getD w false = u.getD w false := by
    induction gs generalizing u with
    | nil => rfl
    | cons g gs ih =>
      exact (ih (step u g) (by simp [step]; omega)).trans (List.getD_append _ _ _ _ h)
  exact H C.gates ws (by simpa [ws] using hw)

private noncomputable def featureBits (C : Circuit) (x y : Shore) :=
  Fin.append (fun i => P C i x) (fun i => L C i y)

private noncomputable def padded (C : Circuit) (z : Fin (countP C + countL C)) (x y : Shore)
    (w : Fin (width C)) :=
  if isPoint C w then pointFeature C w x else
  if isLine C w then lineFeature C w y else featureBits C x y (port C z w)

private theorem padded_pure (C : Circuit) (z) (x y : Shore) (w : Fin (width C))
    (h : isPoint C w ∨ isLine C w) :
    padded C z x y w = wire C (Fin.append x y) w := by
  by_cases hp : isPoint C w
  · rw [padded, ite_eq_left hp]; exact point_factor C w hp x y
  · have hl := h.resolve_left hp
    rw [padded, ite_eq_right hp, ite_eq_left hl]; exact line_factor C w hl x y

private theorem agree_live (C : Circuit) (z) (x y : Shore) (w : Fin (width C)) (hw : w ∈ live C) :
    (featureBits C x y) (port C z w) = padded C z x y w := by
  by_cases hp : isPoint C w
  · have hmem : w ∈ pPorts C := Finset.mem_filter.mpr ⟨hw,hp⟩
    rw [port, dite_eq_left hmem, padded, ite_eq_left hp]
    exact (Fin.append_left (fun i : Fin (countP C) => P C i x) (fun i : Fin (countL C) => L C i y)
      ((pPorts C).equivFin ⟨w,hmem⟩)).trans (by unfold P; rw [Equiv.symm_apply_apply])
  · have hnot : w ∉ pPorts C := fun h => hp (Finset.mem_filter.mp h).2
    by_cases hl : isLine C w
    · have hmem : w ∈ lPorts C := Finset.mem_filter.mpr ⟨hw,hp,hl⟩
      rw [port, dite_eq_right hnot, dite_eq_left hmem, padded, ite_eq_right hp, ite_eq_left hl]
      exact (Fin.append_right (fun i : Fin (countP C) => P C i x) (fun i : Fin (countL C) => L C i y)
        ((lPorts C).equivFin ⟨w,hmem⟩)).trans (by unfold L; rw [Equiv.symm_apply_apply])
    · simp only [padded, ite_eq_right hp, ite_eq_right hl]

theorem cut_eval_of_pure (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 14 C)
    (ho : C.output < width C) (x y : Shore) (t : Fin (width C) → Bool)
    (ht : ∀ w : Fin (width C), isPoint C w ∨ isLine C w → t w = wire C (Fin.append x y) w) :
    (cut C).eval (List.ofFn (t)) = C.eval (List.ofFn (Fin.append x y)) := by
  let raw := Fin.append x y
  let orig := List.ofFn raw
  let b := List.ofFn (t)
  have hoLen : orig.length = 14 := by simp [orig, raw]
  have hbLen : b.length = width C := by simp [b]
  have get (j : Nat) (hj : j < width C) : b.getD j false = t ⟨j,hj⟩ := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_ofFn (f := t) (by simpa using hj)
  have he := eval_extract C orig b (isMixed C) id (hoLen ▸ hC.2.1) (hoLen ▸ ho)
    (by
      intro j hj
      have hj14 : j < 14 := by omega
      have hjw : j < width C := by unfold width; omega
      exact ⟨by simpa only [id_eq, hbLen] using hjw,
        (get j hjw).trans ((ht ⟨j,hjw⟩ (input_pure C j hj14)).trans
          (input_wire C raw j hj14))⟩)
    (by
      intro j _ hj hk
      have hjw : j < width C := by simpa [width, hoLen] using hj
      have hor : isPoint C j ∨ isLine C j := by
        by_contra! h
        exact Bool.noConfusion ((decide_eq_true h).symm.trans hk)
      exact ⟨by simpa only [id_eq, hbLen] using hjw,
        (get j hjw).trans (ht ⟨j,hjw⟩ hor)⟩)
  change (extract C 14 (width C) (isMixed C) id).eval b = C.eval orig
  simpa only [hoLen, hbLen] using he

/-- Distinct one-shore ports counted here are precisely the pure inputs in the
structural support of the output of the mixed circuit. Unused physical ports vanish. -/
theorem compact_factor (C : Circuit) (z) (hC : PEqualNP.TopForm.IsAO2 14 C)
    (ho : C.output < width C) (x y : Shore) :
    FanoMixedSize.mixed (compact C z) (fun i => P C i x) (fun j => L C j y) =
      C.eval (List.ofFn (Fin.append x y)) := by
  let bits := featureBits C x y
  have hrel := (PermInputs.rel_fold _ _ (port C z) (cut C).gates _ _
    (PermInputs.rel_init _ _ (port C z) bits)).2.2 (cut C).output
  exact hrel.trans ((support_agree (cut C) (bits ∘ port C z) (padded C z x y) (cut C).output
    (agree_live C z x y)).trans (cut_eval_of_pure C hC ho x y _ (padded_pure C z x y)))

/-- If the original output distinguishes two inputs, the set of distinct reachable
one-shore ports is nonempty and the fallback required by relabelling exists. -/
theorem port_nonempty (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 14 C) (ho : C.output < width C)
    (x y x' y' : Shore) (hd : C.eval (List.ofFn (Fin.append x y)) ≠
      C.eval (List.ofFn (Fin.append x' y'))) : 0 < countP C + countL C := by
  by_contra! hempty
  change (pPorts C).card + (lPorts C).card ≤ 0 at hempty
  have hP : (pPorts C).card = 0 := by omega
  have hL : (lPorts C).card = 0 := by omega
  have pure_absent (w : Fin (width C)) (hw : w ∈ live C) : ¬(isPoint C w ∨ isLine C w) := by
    rintro (hp | hl)
    · exact (Finset.card_pos.mpr ⟨w,Finset.mem_filter.mpr ⟨hw,hp⟩⟩).ne' hP
    · by_cases hp : isPoint C w
      · exact (Finset.card_pos.mpr ⟨w,Finset.mem_filter.mpr ⟨hw,hp⟩⟩).ne' hP
      · exact (Finset.card_pos.mpr ⟨w,Finset.mem_filter.mpr ⟨hw,hp,hl⟩⟩).ne' hL
  let t (u v : Shore) (w : Fin (width C)) : Bool :=
    if isPoint C w ∨ isLine C w then wire C (Fin.append u v) w else false
  have ht (u v : Shore) (w : Fin (width C)) (hw : isPoint C w ∨ isLine C w) :
      t u v w = wire C (Fin.append u v) w := by simp only [t, ite_eq_left hw]
  have same := support_agree (cut C) (t x y) (t x' y') (cut C).output
    (fun w hw => by simp only [t, ite_eq_right (pure_absent w hw)])
  exact hd (((cut_eval_of_pure C hC ho x y _ (ht x y)).symm.trans same).trans
    (cut_eval_of_pure C hC ho x' y' _ (ht x' y')))

#print axioms compact_factor
#print axioms port_nonempty
end MixedExtract.Fano
