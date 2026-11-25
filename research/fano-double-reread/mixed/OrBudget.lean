import Compression
import PEqualNP.MetaComplexity.Helpers.CoverCircuitList
import FanoFloor

namespace FanoOrBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.CoverCircuit
open FanoBoundary

/-- A nonempty raw signature. Repetitions of literals are allowed, so this also handles lists
before deduplication. Its chain cost is exactly the length of the tail. -/
abbrev Signature (n : Nat) := Fin n × List (Fin n)

def sigVal (s : Signature n) (x : Fin n → Bool) : Bool := x s.1 || s.2.any x

def orCost (ss : List (Signature n)) : Nat := (ss.map (fun s => s.2.length)).sum

private theorem raw_get (pre : List Gate) (x : Fin n → Bool) (a : Fin n) :
    (run pre (List.ofFn x)).getD (a : Nat) false = x a := by
  rw [getD_run _ _ _ (by simp)]
  simp

/-- A shared prefix realizes every listed nonempty signature on the same raw wires. -/
theorem make_prefix (ss : List (Signature n)) :
    ∃ gs : List Gate,
      (∀ g ∈ gs, g.op = GateOp.or ∧ g.inputs.length = 2) ∧ gs.length = orCost ss ∧
      ∀ s ∈ ss, ∃ out : Fin (n + gs.length), ∀ x : Fin n → Bool,
        (run gs (List.ofFn x)).getD out false = sigVal s x := by
  induction ss with
  | nil => exact ⟨[], by simp, rfl, by simp⟩
  | cons s ss ih =>
    obtain ⟨gs, ops, len, ev⟩ := ih
    let start := n + gs.length
    let rest := s.2.map Fin.val
    let block := orChain start s.1.val rest
    have hlen : block.length = s.2.length := by simp [block, rest, orChain_length]
    refine ⟨gs ++ block, ?_, ?_, ?_⟩
    · intro g h
      rcases List.mem_append.mp h with h | h
      · exact ops g h
      · exact orChain_ops _ _ _ g h
    · simp [orCost, hlen, len, Nat.add_comm]
    · intro b hb
      rcases List.mem_cons.mp hb with h | h
      · subst b
        have hs : s.1.val < start := by dsimp [start]; omega
        have hr : ∀ v ∈ rest, v < start := by
          intro v hv
          obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
          dsimp [start]
          omega
        refine ⟨⟨chainOut start s.1.val rest, ?_⟩, ?_⟩
        · have h := chainOut_lt start s.1.val rest hs
          simpa [start, block, orChain_length, Nat.add_assoc] using h
        · intro x
          rw [run_append]
          have hw : (run gs (List.ofFn x)).length = start := by simp [run_length, start]
          change (run (orChain start s.1.val rest) (run gs (List.ofFn x))).getD (chainOut start s.1.val rest) false = _
          rw [orChain_eval _ _ _ _ hw hs hr, raw_get]
          have hraw : (fun a : Fin n => (run gs (List.ofFn x)).getD a.val false) = x :=
            funext fun a => raw_get gs x a
          simpa only [rest, sigVal, List.any_map, Function.comp_def] using
            congrArg (fun f => x s.1 || s.2.any f) hraw
      · obtain ⟨out, hv⟩ := ev b h
        have hot := out.isLt
        refine ⟨⟨out, by simp; omega⟩, ?_⟩
        intro x
        rw [run_append, getD_run block _ _ (by simp [run_length])]
        exact hv x

/-- Prepending one shared OR chain per dictionary row turns a feature-input circuit into
a raw-input circuit. Any number of feature inputs may use the same row. -/
theorem precompose_dictionary {n m s : Nat} (S : Fin m → Signature n) (rows : List (Signature n))
    (covers : ∀ i, S i ∈ rows) (f : (Fin m → Bool) → Bool) (hf : HasCircuitSize m f s) :
    HasCircuitSize n (fun x => f (fun i => sigVal (S i) x)) (s + orCost rows) := by
  obtain ⟨gs, ops, len, ev⟩ := make_prefix rows
  have houts (i : Fin m) := ev (S i) (covers i)
  choose π hp using houts
  obtain ⟨d, hd, hs, he⟩ := Helpers.PermInputs.relabel_size π f s hf
  refine ⟨⟨gs ++ d.gates, d.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨hop, hlen⟩ := ops g hg
      exact ⟨by simp [hop], by omega⟩
    · exact hd g hg
  · change (gs ++ d.gates).length ≤ _
    change d.gates.length ≤ s at hs
    rw [List.length_append, len]
    omega
  · intro x
    let w := run gs (List.ofFn x)
    have hl : w.length = n + gs.length := by simp [w, run_length]
    let z : Fin (n + gs.length) → Bool := fun i => w.getD i.val false
    have hz : List.ofFn z = w := by
      apply List.ext_getElem
      · simp [hl]
      · intro i hi hj
        simp only [List.getElem_ofFn, z]
        exact List.getD_eq_getElem w false hj
    have hv : (z ∘ π) = fun i => sigVal (S i) x := funext fun i => hp i x
    change (run (gs ++ d.gates) (List.ofFn x)).getD d.output false = _
    rw [run_append]
    change d.eval w = _
    rw [← hz, he z]
    exact congrArg f hv

theorem precompose_signatures {n m s : Nat} (S : Fin m → Signature n)
    (f : (Fin m → Bool) → Bool) (hf : HasCircuitSize m f s) :
    HasCircuitSize n (fun x => f (fun i => sigVal (S i) x)) (s + orCost (List.ofFn S)) :=
  precompose_dictionary S (List.ofFn S) (by simp) f hf

#print axioms precompose_dictionary

end FanoOrBudget
