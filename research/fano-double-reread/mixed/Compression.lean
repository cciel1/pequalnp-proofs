import Boundary
import PEqualNP.MetaComplexity.Helpers.PermInputs
import PEqualNP.MetaComplexity.Helpers.LineDegTest

namespace FanoMixedSize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open FanoBoundary

def incident (p l : Fin 7) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3

def edge14 (z : Fin 14 → Bool) : Bool :=
  decide (∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
    z (Fin.castAdd 7 p) = true ∧ z (Fin.natAdd 7 l) = true)

def mixed {a b : Nat} (C : Circuit) (p : Fin a → Bool) (l : Fin b → Bool) : Bool :=
  C.eval (List.ofFn (Fin.append p l))

theorem mixed_mono {a b : Nat} (C : Circuit) (hm : Monotone2 C) :
    MixedMono (@mixed a b C) := by
  intro p q l m hp hl he
  let x := Fin.append p l
  let y := Fin.append q m
  have hxy (i : Fin (a+b)) : x i = true → y i = true := by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simpa [x, y] using hp i
    · simpa [x, y] using hl j
  apply LineDegTest.W_mono C.gates (fun g hg => (hm g hg).1)
    (List.ofFn x) (List.ofFn y) (by simp) _ C.output he
  intro i h
  by_cases hi : i < a + b
  · rw [List.getD_eq_getElem _ _ (by simpa using hi)] at h ⊢
    simpa only [List.getElem_ofFn] using hxy ⟨i,hi⟩ (by simpa using h)
  · rw [List.getD_eq_default _ _ (by simp; omega)] at h
    contradiction

/-- The external wires of the mixed circuit may reuse the same singleton feature.
A size bound for the resulting raw Fano function therefore applies to the mixed circuit itself. -/
theorem raw_size {a b : Nat} (C : Circuit) (hm : Monotone2 C)
    (P : Fin a → Input (Fin 7) → Bool) (L : Fin b → Input (Fin 7) → Bool)
    (hP : ∀ i, MonotoneFeature (P i)) (hL : ∀ j, MonotoneFeature (L j))
    (picks : Fin a → Fin 7) (lines : Fin b → Fin 7)
    (hp : ∀ i v, P i (one v) = true ↔ v = picks i)
    (hl : ∀ j v, L j (one v) = true ↔ v = lines j)
    (computes : ∀ x y, mixed C (fun i => P i x) (fun j => L j y) = true ↔
      AcceptsEdge incident x y) : HasCircuitSize 14 edge14 C.size := by
  let π : Fin (a + b) → Fin 14 := Fin.append (fun i => Fin.castAdd 7 (picks i))
    (fun j => Fin.natAdd 7 (lines j))
  let f : (Fin (a+b) → Bool) → Bool := fun z => C.eval (List.ofFn z)
  have hsize : HasCircuitSize (a+b) f C.size := by
    refine ⟨C, ?_, Nat.le_refl _, fun _ => rfl⟩
    intro g hg
    exact ⟨((hm g hg).1).imp_right Or.inl, (hm g hg).2⟩
  have h := Helpers.PermInputs.relabel_size π f C.size hsize
  suffices (fun z => f (z ∘ π)) = edge14 by rwa [this] at h
  funext z
  let p : Fin 7 → Bool := fun s => z (Fin.castAdd 7 s)
  let l : Fin 7 → Bool := fun s => z (Fin.natAdd 7 s)
  have eqW : (z ∘ π) = Fin.append (fun i => p (picks i)) (fun j => l (lines j)) := by
    funext i
    refine Fin.addCases (fun x => ?_) (fun x => ?_) i <;> simp [π, p, l]
  have eqB := raw_singleton_features_compute_edge (List.finRange 7) (List.finRange 7)
    (by simp) (by simp) incident P L hP hL picks lines hp hl (mixed C) (mixed_mono C hm) computes p l
  rw [eqW]
  change mixed C (fun i => p (picks i)) (fun j => l (lines j)) = edge14 z
  apply Bool.eq_iff_iff.mpr
  simpa only [edge14, decide_eq_true_eq, AcceptsEdge, incident, p, l] using eqB

#print axioms raw_size
end FanoMixedSize
