import BothShores
import OptionalProjection

namespace FanoMixedSize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers FanoBoundary

private def pad {a : Nat} (T : Finset (Fin a)) (v : Input (Fin T.card)) (i : Fin a) : Bool :=
  if hi : i ∈ T then v ((T.orderIsoOfFin rfl).symm ⟨i,hi⟩) else false

private theorem pad_mono {a : Nat} (T : Finset (Fin a)) {v w : Input (Fin T.card)} (h : Below v w) :
    Below (pad T v) (pad T w) := by
  intro i hv
  by_cases hi : i ∈ T
  · simpa [pad, hi] using h ((T.orderIsoOfFin rfl).symm ⟨i,hi⟩) (by simpa [pad, hi] using hv)
  · simp [pad, hi] at hv

private theorem pad_project {a : Nat} (T : Finset (Fin a)) (x : Input (Fin a)) {i : Fin a}
    (hi : i ∈ T) : pad T (fun j => x ((T.orderIsoOfFin rfl) j).val) i = x i := by
  simp [pad, hi]

/-- Retain just the primary ports in the structural support of the output. -/
theorem restrict_mixed_ports {a b : Nat} (C : Circuit) (hm : Monotone2 C)
    (P : Fin a → Input (Fin 7) → Bool) (L : Fin b → Input (Fin 7) → Bool)
    (hP : ∀ i, MonotoneFeature (P i)) (hL : ∀ j, MonotoneFeature (L j))
    (computes : ∀ x y, mixed C (fun i => P i x) (fun j => L j y) = true ↔
      AcceptsEdge incident x y) : 
    ∃ (u v : Nat) (p : Fin u → Fin a) (l : Fin v → Fin b)
      (M : Input (Fin u) → Input (Fin v) → Bool),
      u + v ≤ C.size + 1 ∧ 7 ≤ u ∧ 7 ≤ v ∧ MixedMono M ∧
      (∀ x y, M (fun i => P (p i) x) (fun j => L (l j) y) = true ↔ AcceptsEdge incident x y) ∧
      HasCircuitSize (u+v) (fun z => M (z ∘ Fin.castAdd v) (z ∘ Fin.natAdd u)) C.size := by
  classical
  let S := (suppsFrom C.gates (inputSupps (a+b))).getD C.output ∅
  let T := Finset.univ.filter (fun i : Fin a => Fin.castAdd b i ∈ S)
  let U := Finset.univ.filter (fun i : Fin b => Fin.natAdd a i ∈ S)
  let M := fun p l => mixed C (pad T p) (pad U l)
  have hMon : MixedMono M := fun _ _ _ _ h k => mixed_mono C hm _ _ _ _ (pad_mono T h) (pad_mono U k)
  let P' := fun j : Fin T.card => P ((T.orderIsoOfFin rfl) j).val
  let L' := fun j : Fin U.card => L ((U.orderIsoOfFin rfl) j).val
  have old (x y : Input (Fin 7)) :
      M (fun i => P' i x) (fun j => L' j y) = mixed C (fun i => P i x) (fun j => L j y) := by
    apply (agree_wiresFrom _ _ C.gates _ _ _ (agree_inputs _ _)).2.2 C.output
    intro w
    refine Fin.addCases (fun i => ?_) (fun i => ?_) w
    · intro hi
      simpa only [Fin.append_left] using pad_project T (fun i => P i x) (i := i) (by simpa [T, S] using hi)
    · intro hi
      simpa only [Fin.append_right] using pad_project U (fun i => L i y) (i := i) (by simpa [U, S] using hi)
  have ⟨ht, hu⟩ := seven_features_each P' L' (fun i => hP _) (fun i => hL _) M hMon
    (by intro x y; rw [old]; exact computes x y)
  let inj : T ⊕ U → S := Sum.elim
    (fun i => ⟨Fin.castAdd b i.val, (Finset.mem_filter.mp i.property).2⟩)
    (fun j => ⟨Fin.natAdd a j.val, (Finset.mem_filter.mp j.property).2⟩)
  have hinj : Function.Injective inj := by
    rintro (i|i) (j|j) heq <;> have hv := congrArg (fun z : S => z.val.val) heq <;>
      simp only [inj, Sum.elim_inl, Sum.elim_inr, Fin.val_castAdd, Fin.val_natAdd] at hv
    · exact congrArg Sum.inl (Subtype.ext (Fin.ext hv))
    · have := i.val.isLt; omega
    · have := j.val.isLt; omega
    · exact congrArg Sum.inr (Subtype.ext (Fin.ext (by omega)))
  have htotal := Fintype.card_le_of_injective inj hinj
  simp only [Fintype.card_sum, Fintype.card_coe] at htotal
  have hok : ∀ g ∈ C.gates, Ok g := fun g h => ⟨((hm g h).1).imp_right Or.inl, (hm g h).2⟩
  have hc := cnt_suppsFrom C.gates 0 (inputSupps (a+b)) hok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  change S.card ≤ C.size + 1 at hc
  refine ⟨T.card, U.card, fun i => ((T.orderIsoOfFin rfl) i).val, fun i => ((U.orderIsoOfFin rfl) i).val,
    M, by omega, ht, hu, hMon, ?_, ?_⟩
  · intro x y
    exact (old x y) ▸ computes x y
  · let π : Fin (a+b) → Option (Fin (T.card+U.card)) := Fin.append
      (fun i => if h : i ∈ T then some (Fin.castAdd U.card ((T.orderIsoOfFin rfl).symm ⟨i,h⟩)) else none)
      (fun j => if h : j ∈ U then some (Fin.natAdd T.card ((U.orderIsoOfFin rfl).symm ⟨j,h⟩)) else none)
    let f : Input (Fin (a+b)) → Bool := fun z => C.eval (List.ofFn z)
    have raw : HasCircuitSize (a+b) f C.size := ⟨C, hok, le_rfl, fun _ => rfl⟩
    have opt := optional_projection π f raw
    suffices eqf : (fun z => f (fun i => (π i).elim false z)) =
      (fun z => M (z ∘ Fin.castAdd U.card) (z ∘ Fin.natAdd T.card)) by rwa [eqf] at opt
    funext z
    change C.eval (List.ofFn _) = C.eval (List.ofFn _)
    congr 2
    funext w
    refine Fin.addCases (fun i => ?_) (fun j => ?_) w
    · by_cases h : i ∈ T <;> simp [π, pad, h, Function.comp_apply]
    · by_cases h : j ∈ U <;> simp [π, pad, h, Function.comp_apply]

/-- Any binary mixed core computing Fano incidence after monotone, one-shore
preprocessing needs thirteen gates, irrespective of the pure features or their number. -/
theorem arbitrary_mixed_floor {a b : Nat} (C : Circuit) (hm : Monotone2 C)
    (P : Fin a → Input (Fin 7) → Bool) (L : Fin b → Input (Fin 7) → Bool)
    (hP : ∀ i, MonotoneFeature (P i)) (hL : ∀ j, MonotoneFeature (L j))
    (computes : ∀ x y, mixed C (fun i => P i x) (fun j => L j y) = true ↔
      AcceptsEdge incident x y) : 13 ≤ C.size := by
  obtain ⟨u,v,_,_,_,ht,h1,h2,_⟩ := restrict_mixed_ports C hm P L hP hL computes
  omega

#print axioms restrict_mixed_ports
#print axioms arbitrary_mixed_floor
end FanoMixedSize
