import Numeric
import OptionalProjection

namespace FanoMixedSize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity FanoBoundary

private theorem lin_optional {α : Type} [DecidableEq α] (all : List α)
    (full : ∀ a, a ∈ all) (F : Input α → Bool) (o : Option α)
    (sig : ∀ v, F (one v) = true ↔ o = some v) (x : Input α) :
    lin all F x = o.elim false x := by
  cases o with
  | none =>
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨v, _, _, hv⟩ := (lin_spec _ _ _).mp h
    have e := (sig v).mp hv
    cases e
  | some a =>
    apply lin_single_signature _ full _ a _ _
    intro v
    constructor
    · intro hv
      exact (Option.some.inj ((sig v).mp hv)).symm
    · intro hv
      exact (sig v).mpr (congrArg some hv.symm)

/-- An empty singleton signature needs no gate. All mixed-core ports can thus use
an empty or singleton signature, even when several ports share the same literal. -/
theorem at_most_one_mixed_floor {a b : Nat} (C : Circuit) (hm : Monotone2 C)
    (P : Fin a → Input (Fin 7) → Bool) (L : Fin b → Input (Fin 7) → Bool)
    (hP : ∀ i, MonotoneFeature (P i)) (hL : ∀ j, MonotoneFeature (L j))
    (picks : Fin a → Option (Fin 7)) (lines : Fin b → Option (Fin 7))
    (hp : ∀ i v, P i (one v) = true ↔ picks i = some v)
    (hl : ∀ j v, L j (one v) = true ↔ lines j = some v)
    (computes : ∀ x y, mixed C (fun i => P i x) (fun j => L j y) = true ↔
      AcceptsEdge incident x y) : 20 ≤ C.size := by
  let π : Fin (a+b) → Option (Fin 14) := Fin.append
    (fun i => (picks i).map (Fin.castAdd 7)) (fun j => (lines j).map (Fin.natAdd 7))
  let f : (Fin (a+b) → Bool) → Bool := fun z => C.eval (List.ofFn z)
  have hsize : HasCircuitSize (a+b) f C.size := by
    refine ⟨C, ?_, Nat.le_refl _, fun _ => rfl⟩
    intro g hg
    exact ⟨((hm g hg).1).imp_right Or.inl, (hm g hg).2⟩
  apply FanoFloor.floor
  have hr := optional_projection π f hsize
  suffices eqF : (fun z => f (fun i => (π i).elim false z)) = edge14 by rwa [eqF] at hr
  funext z
  let p : Fin 7 → Bool := fun s => z (Fin.castAdd 7 s)
  let l : Fin 7 → Bool := fun s => z (Fin.natAdd 7 s)
  let points := List.finRange 7
  have full (a : Fin 7) : a ∈ points := by simp [points]
  have e : (fun i => (π i).elim false z) =
      Fin.append (fun i => lin points (P i) p) (fun j => lin points (L j) l) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp only [π, Fin.append_left, lin_optional points full (P i) (picks i) (hp i) p]
      cases picks i <;> rfl
    · simp only [π, Fin.append_right, lin_optional points full (L j) (lines j) (hl j) l]
      cases lines j <;> rfl
  rw [e]
  change mixed C _ _ = edge14 z
  apply Bool.eq_iff_iff.mpr
  simpa only [edge14, decide_eq_true_eq, AcceptsEdge, incident, p, l] using
    normalize_edge_function points points full full incident P L hP hL (mixed C)
      (mixed_mono C hm) computes p l

#print axioms at_most_one_mixed_floor
end FanoMixedSize
