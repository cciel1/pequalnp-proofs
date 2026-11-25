import FanoBudget

namespace FanoOrBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open FanoBoundary FanoMixedSize

/-- The enumerable singleton support, including the empty support. -/
def support (F : Input (Fin n) → Bool) : List (Fin n) :=
  (List.finRange n).filter fun i => F (one i)

theorem support_eval (F : Input (Fin n) → Bool) (x : Input (Fin n)) :
    (support F).any x = lin (List.finRange n) F x := by
  apply Bool.eq_iff_iff.mpr
  rw [lin_spec]
  simp only [support, List.any_eq_true, List.mem_filter, List.mem_finRange, true_and]
  exact exists_congr fun _ => and_comm

def splitSig (row : List (Fin n)) : Option (Signature n) :=
  match row with
  | [] => none
  | a :: rest => some (a, rest)

/-- Each distinct nonempty signature gets one shared OR chain. -/
def dictionary (S : Fin m → List (Fin n)) : List (Signature n) :=
  ((List.ofFn S).filterMap splitSig).dedup

theorem dictionary_covers (S : Fin m → List (Fin n)) (i : Fin m) (a : Fin n)
    (rest : List (Fin n)) (eq : S i = a :: rest) : (a, rest) ∈ dictionary S := by
  apply List.mem_dedup.mpr
  exact List.mem_filterMap.mpr ⟨S i, by simp, by simp [eq, splitSig]⟩

/-- Empty rows use the zero-cost false projection, and the others share the prefix. -/
theorem precompose_lists {n m s : Nat} (S : Fin m → List (Fin n)) (rows : List (Signature n))
    (cover : ∀ i a rest, S i = a :: rest → (a, rest) ∈ rows)
    (f : (Fin m → Bool) → Bool) (hf : HasCircuitSize m f s) :
    HasCircuitSize n (fun x => f (fun i => (S i).any x)) (s + orCost rows) := by
  have lookup (i : Fin m) : ∃ p : Option (Fin rows.length), ∀ x : Input (Fin n),
      p.elim false (fun k => sigVal (rows.get k) x) = (S i).any x := by
    cases h : S i with
    | nil => exact ⟨none, fun _ => rfl⟩
    | cons a rest =>
      obtain ⟨k, hk⟩ := List.mem_iff_get.mp (cover i a rest h)
      exact ⟨some k, fun x => by simp only [Option.elim_some, hk, sigVal, List.any_cons]⟩
  choose pick hp using lookup
  let body : (Fin rows.length → Bool) → Bool := fun z => f (fun i => (pick i).elim false z)
  have hb : HasCircuitSize rows.length body s := optional_projection pick f hf
  have result := precompose_dictionary rows.get rows (fun i => List.get_mem ..) body hb
  suffices (fun x => body (fun k => sigVal (rows.get k) x)) = (fun x => f fun i => (S i).any x) by
    rwa [this] at result
  funext x
  exact congrArg f (funext fun i => hp i x)

/-- Canonical raw supports concatenate the two lists on their respective shores. -/
def rawSupports (P : Fin a → Input (Fin 7) → Bool) (L : Fin b → Input (Fin 7) → Bool) :
    Fin (a+b) → List (Fin 14) :=
  Fin.append (fun i => (support (P i)).map (Fin.castAdd 7))
    (fun j => (support (L j)).map (Fin.natAdd 7))

theorem raw_fano_any_size {a b : Nat} (C : Circuit) (hm : Monotone2 C)
    (P : Fin a → Input (Fin 7) → Bool) (L : Fin b → Input (Fin 7) → Bool)
    (hP : ∀ i, MonotoneFeature (P i)) (hL : ∀ j, MonotoneFeature (L j))
    (computes : ∀ x y, mixed C (fun i => P i x) (fun j => L j y) = true ↔
      AcceptsEdge incident x y)
    (rows : List (Signature 14))
    (cover : ∀ i a rest, rawSupports P L i = a :: rest → (a, rest) ∈ rows) :
    HasCircuitSize 14 edge14 (C.size + orCost rows) := by
  let f : (Fin (a+b) → Bool) → Bool := fun z => C.eval (List.ofFn z)
  have hsize : HasCircuitSize (a+b) f C.size := by
    refine ⟨C, ?_, Nat.le_refl _, fun _ => rfl⟩
    intro g hg
    exact ⟨((hm g hg).1).imp_right Or.inl, (hm g hg).2⟩
  have h := precompose_lists (rawSupports P L) rows cover f hsize
  suffices (fun z => f fun i => (rawSupports P L i).any z) = edge14 by rwa [this] at h
  funext z
  let p : Fin 7 → Bool := z ∘ Fin.castAdd 7
  let l : Fin 7 → Bool := z ∘ Fin.natAdd 7
  have eqW : (fun i => (rawSupports P L i).any z) =
      Fin.append (fun i => lin (List.finRange 7) (P i) p) (fun j => lin (List.finRange 7) (L j) l) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simpa only [rawSupports, Fin.append_left, List.any_map] using support_eval (P i) p
    · simpa only [rawSupports, Fin.append_right, List.any_map] using support_eval (L j) l
  rw [eqW]
  change mixed C (fun i => lin (List.finRange 7) (P i) p) (fun j => lin (List.finRange 7) (L j) l) = edge14 z
  have eqB := normalize_edge_function (List.finRange 7) (List.finRange 7) (by simp) (by simp)
    incident P L hP hL (mixed C) (mixed_mono C hm) computes p l
  exact Bool.eq_iff_iff.mpr (by simpa only [edge14, decide_eq_true_eq, AcceptsEdge, incident, p, l,
    Function.comp_apply] using eqB)

/-- For every monotone pure-feature decomposition of Fano incidence, the mixed size plus the
sum of (width−1) over distinct nonempty singleton supports is at least twenty. -/
theorem arbitrary_fano_budget {a b : Nat} (C : Circuit) (hm : Monotone2 C)
    (P : Fin a → Input (Fin 7) → Bool) (L : Fin b → Input (Fin 7) → Bool)
    (hP : ∀ i, MonotoneFeature (P i)) (hL : ∀ j, MonotoneFeature (L j))
    (computes : ∀ x y, mixed C (fun i => P i x) (fun j => L j y) = true ↔
      AcceptsEdge incident x y) :
    20 ≤ C.size + orCost (dictionary (rawSupports P L)) :=
  FanoFloor.floor (raw_fano_any_size C hm P L hP hL computes _ (dictionary_covers _))

#print axioms raw_fano_any_size
#print axioms arbitrary_fano_budget
end FanoOrBudget
