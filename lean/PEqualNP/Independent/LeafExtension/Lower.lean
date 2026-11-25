import PEqualNP.Independent.LeafExtension.Graph
import PEqualNP.MetaComplexity.L014

namespace Independent.LeafExtension

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {n k s : ℕ}

@[simp] theorem edgeFun_singleton (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    edgeFun G (fun i => decide (i = v)) = false := by
  simp [edgeFun]

theorem edgeFun_nonconstant (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (he : ∃ i j, G.Adj i j) :
    ∃ x y, edgeFun G x ≠ edgeFun G y := by
  exact ⟨fun _ => true, fun _ => false, by simp [edgeFun, he]⟩

/-- A zero-gate output is an input or false. Neither computes a nonempty graph. -/
theorem edgeFun_size_pos (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (he : ∃ i j, G.Adj i j)
    (h : HasCircuitSize n (edgeFun G) s) : 0 < s := by
  by_contra! hz
  obtain ⟨⟨gs, out⟩, _, hsz, ev⟩ := h
  have hnil : gs = [] := List.length_eq_zero_iff.mp (by simpa [Circuit.size] using hsz.trans hz)
  subst gs
  by_cases ho : out < n
  · let v : Fin n := ⟨out, ho⟩
    have hh := ev (fun i => decide (i = v))
    rw [edgeFun_singleton] at hh
    simpa [Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD,
      ho, v] using hh
  · have hh := ev (fun _ => true)
    change (List.ofFn (fun _ : Fin n => true)).getD out false = _ at hh
    rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt ho)] at hh
    simp [edgeFun, he] at hh

@[simp] theorem edgeFun_addLeaf_snoc (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n)
    (x : Fin n → Bool) (b : Bool) :
    edgeFun (addLeaf G v) (Fin.snoc x b) = (edgeFun G x || (x v && b)) := by
  simp [edgeFun_addLeaf, PEqualNP.PendantBit.pendF]

/-- A circuit on the extension yields an old circuit with a strictly smaller budget. -/
theorem eliminate_leaf (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n)
    (he : ∃ i j, G.Adj i j) (h : HasCircuitSize (n+1) (edgeFun (addLeaf G v)) s) :
    ∃ t, HasCircuitSize n (edgeFun G) t ∧ t+1 ≤ s := by
  have hpos := edgeFun_size_pos (addLeaf G v) ⟨_, _, (addLeaf_adj_last G v _).mpr rfl⟩ h
  obtain ⟨t, rfl⟩ : ∃ t, s = t+1 := ⟨s-1, by omega⟩
  have hdep : ∃ x : Fin (n+1) → Bool,
      edgeFun (addLeaf G v) (Function.update x (Fin.last n) (!x (Fin.last n))) ≠
        edgeFun (addLeaf G v) x := by
    let y : Fin n → Bool := fun i => decide (i = v)
    refine ⟨Fin.snoc y false, ?_⟩
    rw [Fin.snoc_last, Bool.not_false, Fin.update_snoc_last]
    simp [y]
  have hnc : ∃ x y : Fin n → Bool,
      edgeFun (addLeaf G v) (Fin.snoc x false) ≠ edgeFun (addLeaf G v) (Fin.snoc y false) := by
    simpa using edgeFun_nonconstant G he
  refine ⟨t, ?_, le_rfl⟩
  simpa using L014 n _ false t hdep hnc h

/-- The lower bound is independent of any cover or optimality assumption. -/
theorem eliminate_leaves (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : Fin k → Fin n)
    (he : ∃ i j, G.Adj i j) (h : HasCircuitSize (n+k) (edgeFun (attach G k a)) s) :
    ∃ t, HasCircuitSize n (edgeFun G) t ∧ t+k ≤ s := by
  induction k generalizing s with
  | zero => exact ⟨s, h, le_rfl⟩
  | succ k ih =>
    let b : Fin k → Fin n := fun j => a j.castSucc
    obtain ⟨u, hu, hus⟩ := eliminate_leaf (attach G k b) (Fin.castAdd k (a (Fin.last k)))
      (attach_hasEdge G b he) h
    obtain ⟨t, ht, htu⟩ := ih b hu
    exact ⟨t, ht, by omega⟩

end Independent.LeafExtension
