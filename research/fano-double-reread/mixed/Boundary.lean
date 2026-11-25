import Init

namespace FanoBoundary

abbrev Input (α : Type u) := α → Bool

def Below (x y : Input α) : Prop := ∀ a, x a = true → y a = true

def MonotoneFeature (F : Input α → Bool) : Prop :=
  ∀ x y, Below x y → F x = true → F y = true

def one [DecidableEq α] (a : α) : Input α := fun b => decide (b = a)

def zero : Input α := fun _ => false

theorem one_below [DecidableEq α] {x : Input α} {a : α} (hx : x a = true) :
    Below (one a) x := by
  intro b hb
  have h : b = a := of_decide_eq_true hb
  exact h ▸ hx

/-- The OR of the active inputs whose singleton the original feature accepts. -/
def lin [DecidableEq α] (all : List α) (F : Input α → Bool) (x : Input α) : Bool :=
  all.any fun a => x a && F (one a)

theorem lin_spec [DecidableEq α] (all : List α) (F : Input α → Bool) (x : Input α) :
    lin all F x = true ↔ ∃ a, a ∈ all ∧ x a = true ∧ F (one a) = true := by
  simp [lin, List.any_eq_true, Bool.and_eq_true]

private theorem bool_ext {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

theorem lin_below [DecidableEq α] (all : List α) {F : Input α → Bool} (hF : MonotoneFeature F)
    (x : Input α) (hx : lin all F x = true) : F x = true := by
  obtain ⟨a, _, ha, h⟩ := (lin_spec _ _ _).mp hx
  exact hF _ _ (one_below ha) h

theorem lin_mono [DecidableEq α] (all : List α) (F : Input α → Bool) :
    MonotoneFeature (lin all F) := by
  intro x y hxy h
  obtain ⟨a, hm, ha, hf⟩ := (lin_spec _ _ _).mp h
  exact (lin_spec _ _ _).mpr ⟨a, hm, hxy a ha, hf⟩

theorem lin_zero [DecidableEq α] (all : List α) (F : Input α → Bool) :
    lin all F zero = false := by
  cases h : lin all F zero with
  | false => rfl
  | true =>
    obtain ⟨_, _, hbad, _⟩ := (lin_spec _ _ _).mp h
    contradiction

theorem lin_agrees_zero [DecidableEq α] (all : List α) {F : Input α → Bool}
    (hF : F zero = false) : lin all F zero = F zero := (lin_zero all F).trans hF.symm

theorem lin_one [DecidableEq α] (all : List α) (complete : ∀ a, a ∈ all)
    (F : Input α → Bool) (a : α) : lin all F (one a) = F (one a) := by
  apply bool_ext
  constructor
  · intro hx
    obtain ⟨b, _, hb, hF⟩ := (lin_spec _ _ _).mp hx
    have e : b = a := of_decide_eq_true hb
    simpa only [e] using hF
  · intro hF
    exact (lin_spec _ _ _).mpr ⟨a, complete a, by simp [one], hF⟩

/-- A singleton signature is implemented by a wire directly from its raw input. -/
theorem lin_single_signature [DecidableEq α] (all : List α) (complete : ∀ a, a ∈ all)
    (F : Input α → Bool) (a : α) (signature : ∀ b, F (one b) = true ↔ b = a)
    (x : Input α) : lin all F x = x a := by
  apply bool_ext
  constructor
  · intro hx
    obtain ⟨b, _, hb, hs⟩ := (lin_spec _ _ _).mp hx
    simpa only [(signature b).mp hs] using hb
  · intro ha
    exact (lin_spec _ _ _).mpr ⟨a, complete a, ha, (signature a).mpr rfl⟩

def MixedMono (M : Input ι → Input κ → Bool) : Prop :=
  ∀ p q l m, Below p q → Below l m → M p l = true → M q m = true

def AcceptsEdge (E : α → β → Prop) (x : Input α) (y : Input β) : Prop :=
  ∃ a b, E a b ∧ x a = true ∧ y b = true

/-- Any monotone mixed computation of a bipartite edge function still computes it after
each shore's feature is replaced by its OR of singleton witnesses. -/
theorem normalize_edge_function [DecidableEq α] [DecidableEq β]
    (points : List α) (lines : List β) (allP : ∀ a, a ∈ points) (allL : ∀ b, b ∈ lines)
    (E : α → β → Prop) (P : ι → Input α → Bool) (L : κ → Input β → Bool)
    (hP : ∀ i, MonotoneFeature (P i)) (hL : ∀ j, MonotoneFeature (L j))
    (M : Input ι → Input κ → Bool) (hM : MixedMono M)
    (correct : ∀ x y, M (fun i => P i x) (fun j => L j y) = true ↔ AcceptsEdge E x y)
    (x : Input α) (y : Input β) :
    M (fun i => lin points (P i) x) (fun j => lin lines (L j) y) = true ↔ AcceptsEdge E x y := by
  constructor
  · intro h
    apply (correct x y).mp
    exact hM _ _ _ _ (fun i => lin_below points (hP i) x)
      (fun j => lin_below lines (hL j) y) h
  · rintro ⟨a, b, he, ha, hb⟩
    have singletonAccepted := (correct (one a) (one b)).mpr
      ⟨a, b, he, by simp [one], by simp [one]⟩
    apply hM _ _ _ _ _ _ singletonAccepted
    · intro i h
      exact (lin_spec _ _ _).mpr ⟨a, allP a, ha, h⟩
    · intro j h
      exact (lin_spec _ _ _).mpr ⟨b, allL b, hb, h⟩

/-- When every pure feature on both shores has one accepting singleton, all features
can be replaced by raw inputs, leaving the mixed computation unchanged. -/
theorem raw_singleton_features_compute_edge [DecidableEq α] [DecidableEq β]
    (points : List α) (lines : List β) (allP : ∀ a, a ∈ points) (allL : ∀ b, b ∈ lines)
    (E : α → β → Prop) (P : ι → Input α → Bool) (L : κ → Input β → Bool)
    (hP : ∀ i, MonotoneFeature (P i)) (hL : ∀ j, MonotoneFeature (L j))
    (pickP : ι → α) (pickL : κ → β)
    (sigP : ∀ i a, P i (one a) = true ↔ a = pickP i)
    (sigL : ∀ j b, L j (one b) = true ↔ b = pickL j)
    (M : Input ι → Input κ → Bool) (hM : MixedMono M)
    (correct : ∀ x y, M (fun i => P i x) (fun j => L j y) = true ↔ AcceptsEdge E x y)
    (x : Input α) (y : Input β) :
    M (fun i => x (pickP i)) (fun j => y (pickL j)) = true ↔ AcceptsEdge E x y := by
  have pointWires : (fun i => lin points (P i) x) = (fun i => x (pickP i)) :=
    funext fun i => lin_single_signature points allP (P i) (pickP i) (sigP i) x
  have lineWires : (fun j => lin lines (L j) y) = (fun j => y (pickL j)) :=
    funext fun j => lin_single_signature lines allL (L j) (pickL j) (sigL j) y
  simpa only [pointWires, lineWires] using
    normalize_edge_function points lines allP allL E P L hP hL M hM correct x y

#print axioms raw_singleton_features_compute_edge

#print axioms lin_one
#print axioms lin_single_signature
#print axioms normalize_edge_function

end FanoBoundary
