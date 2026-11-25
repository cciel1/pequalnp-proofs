import OrBudget
import OptionalProjection

namespace FanoOrBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open FanoBoundary FanoMixedSize

/-- Renaming raw wires does not change the value or the cost of their OR chain. -/
def mapSig (f : Fin n → Fin k) (s : Signature n) : Signature k := (f s.1, s.2.map f)

theorem sigVal_map (f : Fin n → Fin k) (s : Signature n) (x : Fin k → Bool) :
    sigVal (mapSig f s) x = sigVal s (x ∘ f) := by
  simp only [sigVal, mapSig, List.any_map, Function.comp_def]

theorem sigVal_eq_lin (s : Signature n) (F : Input (Fin n) → Bool)
    (h : ∀ v, F (one v) = true ↔ v ∈ s.1 :: s.2) (x : Input (Fin n)) :
    sigVal s x = lin (List.finRange n) F x := by
  apply Bool.eq_iff_iff.mpr
  rw [lin_spec]
  simp only [sigVal, Bool.or_eq_true, List.any_eq_true, List.mem_finRange, true_and]
  constructor
  · rintro (hx | ⟨v, hv, hx⟩)
    · exact ⟨s.1, hx, (h _).mpr (List.mem_cons_self ..)⟩
    · exact ⟨v, hx, (h _).mpr (List.mem_cons_of_mem _ hv)⟩
  · rintro ⟨v,hv,hF⟩
    rcases List.mem_cons.mp ((h v).mp hF) with e | hm
    · exact Or.inl (e ▸ hv)
    · exact Or.inr ⟨v,hm,hv⟩

/-- Concatenate the point-feature and line-feature signatures on their respective raw shores. -/
def joint (points : Fin a → Signature 7) (lines : Fin b → Signature 7) :
    Fin (a+b) → Signature 14 :=
  Fin.append (fun i => mapSig (Fin.castAdd 7) (points i))
    (fun j => mapSig (Fin.natAdd 7) (lines j))

/-- Nonempty pure-feature signatures can be implemented at the cost of their distinct shared
dictionary rows.  A single row may feed arbitrarily many mixed-circuit inputs. -/
theorem raw_fano_size {a b : Nat} (C : Circuit) (hm : Monotone2 C)
    (P : Fin a → Input (Fin 7) → Bool) (L : Fin b → Input (Fin 7) → Bool)
    (hP : ∀ i, MonotoneFeature (P i)) (hL : ∀ j, MonotoneFeature (L j))
    (pS : Fin a → Signature 7) (lS : Fin b → Signature 7)
    (hp : ∀ i v, P i (one v) = true ↔ v ∈ (pS i).1 :: (pS i).2)
    (hl : ∀ j v, L j (one v) = true ↔ v ∈ (lS j).1 :: (lS j).2)
    (computes : ∀ x y, mixed C (fun i => P i x) (fun j => L j y) = true ↔
      AcceptsEdge incident x y)
    (rows : List (Signature 14)) (cover : ∀ i, joint pS lS i ∈ rows) :
    HasCircuitSize 14 edge14 (C.size + orCost rows) := by
  let f : (Fin (a+b) → Bool) → Bool := fun z => C.eval (List.ofFn z)
  have hsize : HasCircuitSize (a+b) f C.size := by
    refine ⟨C, ?_, Nat.le_refl _, fun _ => rfl⟩
    intro g hg
    exact ⟨((hm g hg).1).imp_right Or.inl, (hm g hg).2⟩
  have h := precompose_dictionary (joint pS lS) rows cover f hsize
  suffices (fun z => f fun i => sigVal (joint pS lS i) z) = edge14 by rwa [this] at h
  funext z
  let p : Fin 7 → Bool := z ∘ Fin.castAdd 7
  let l : Fin 7 → Bool := z ∘ Fin.natAdd 7
  have eqW : (fun i => sigVal (joint pS lS i) z) =
      Fin.append (fun i => lin (List.finRange 7) (P i) p) (fun j => lin (List.finRange 7) (L j) l) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simpa only [joint, Fin.append_left, sigVal_map] using sigVal_eq_lin (pS i) (P i) (hp i) p
    · simpa only [joint, Fin.append_right, sigVal_map] using sigVal_eq_lin (lS j) (L j) (hl j) l
  rw [eqW]
  change mixed C (fun i => lin (List.finRange 7) (P i) p) (fun j => lin (List.finRange 7) (L j) l) = edge14 z
  have eqB := normalize_edge_function (List.finRange 7) (List.finRange 7) (by simp) (by simp)
    incident P L hP hL (mixed C) (mixed_mono C hm) computes p l
  exact Bool.eq_iff_iff.mpr (by simpa only [edge14, decide_eq_true_eq, AcceptsEdge, incident, p, l,
    Function.comp_apply] using eqB)

/-- A mixed circuit of k gates requires at least 20−k additional gates in any of the
explicit OR-prefix implementations above. -/
theorem fano_budget {a b : Nat} (C : Circuit) (hm : Monotone2 C)
    (P : Fin a → Input (Fin 7) → Bool) (L : Fin b → Input (Fin 7) → Bool)
    (hP : ∀ i, MonotoneFeature (P i)) (hL : ∀ j, MonotoneFeature (L j))
    (pS : Fin a → Signature 7) (lS : Fin b → Signature 7)
    (hp : ∀ i v, P i (one v) = true ↔ v ∈ (pS i).1 :: (pS i).2)
    (hl : ∀ j v, L j (one v) = true ↔ v ∈ (lS j).1 :: (lS j).2)
    (computes : ∀ x y, mixed C (fun i => P i x) (fun j => L j y) = true ↔
      AcceptsEdge incident x y)
    (rows : List (Signature 14)) (cover : ∀ i, joint pS lS i ∈ rows) :
    20 ≤ C.size + orCost rows :=
  FanoFloor.floor (raw_fano_size C hm P L hP hL pS lS hp hl computes rows cover)

#print axioms fano_budget
end FanoOrBudget
