import PEqualNP.Independent.PendantCycle.Basic
import PEqualNP.MetaComplexity.L014
import PEqualNP.MetaComplexity.L106

namespace Independent.PendantCycle

open PEqualNP.MetaComplexity

/-- The last leaf adds exactly the new edge from the hub to that input. -/
private theorem snoc_leaf {n k : ℕ} (hn : 0 < n) (y : Fin (n+k) → Bool) (b : Bool) :
    edgeFun n (k+1) hn (Fin.snoc y b) =
      (edgeFun n k hn y || (y (Fin.castAdd k ⟨n-1, by omega⟩) && b)) := by
  have hcast (i : Fin n) : (Fin.snoc y b : Fin (n+k+1) → Bool) (Fin.castAdd (k+1) i) =
      y (Fin.castAdd k i) := by
    change (Fin.snoc y b : Fin (n+k+1) → Bool) (Fin.castAdd k i).castSucc = _
    rw [Fin.snoc_castSucc]
  have hlast : (Fin.snoc y b : Fin (n+k+1) → Bool) (Fin.natAdd n (Fin.last k)) = b := by
    change (Fin.snoc y b : Fin (n+k+1) → Bool) (Fin.last (n+k)) = b
    rw [Fin.snoc_last]
  simp only [edgeFun, hcast, Fin.exists_fin_succ', Fin.natAdd_castSucc, Fin.snoc_castSucc,
    hlast, Bool.decide_or, Bool.decide_eq_true, Bool.and_or_distrib_left, Bool.or_assoc]

private theorem only_hub {n k : ℕ} (hn : 5 ≤ n) :
    edgeFun n k (by omega) (fun i => decide (i.val = n-1)) = false := by
  have hc : ¬ ∃ i j : Fin n, (i.val + 1) % n = j.val ∧ i.val = n - 1 ∧ j.val = n - 1 := by
    rintro ⟨i, j, hij, hi, hj⟩
    rw [hi, hj, show n - 1 + 1 = n by omega, Nat.mod_self] at hij
    omega
  have hl : ¬ ∃ j : Fin k, n + j.val = n-1 := by rintro ⟨j,hj⟩; omega
  simp [edgeFun, hc, hl]

private theorem old_nonconstant {n k : ℕ} (hn : 5 ≤ n) :
    ∃ x y : Fin (n+k) → Bool, edgeFun n k (by omega) x ≠ edgeFun n k (by omega) y := by
  refine ⟨fun _ => true, fun _ => false, ?_⟩
  have he : ∃ i j : Fin n, (i.val+1) % n = j.val := by
    refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
    change 1 % n = 1
    exact Nat.mod_eq_of_lt (by omega)
  simp [edgeFun, he]

/-- Deleting each pendant input costs at least one gate, after which the cycle bound applies. -/
theorem lower {n k s : ℕ} (hn : 5 ≤ n) (h : HasCircuitSize (n+k) (edgeFun n k (by omega)) s) :
    n + (n+1)/2 + k ≤ s + 1 := by
  induction k generalizing s with
  | zero =>
    have hbase : edgeFun n 0 (by omega) = fun y : Fin n → Bool => decide (∃ i j : Fin n,
        (i.val+1) % n = j.val ∧ y i = true ∧ y j = true) := by
      funext y
      simp [edgeFun]
    rw [hbase] at h
    have hc := (L106 n s hn).mp h
    simpa using hc
  | succ k ih =>
    have hdep : ∃ x : Fin (n+k+1) → Bool,
        edgeFun n (k+1) (by omega) (Function.update x (Fin.last (n+k)) (! x (Fin.last (n+k)))) ≠
          edgeFun n (k+1) (by omega) x := by
      let y : Fin (n+k) → Bool := fun i => decide (i.val = n-1)
      refine ⟨Fin.snoc y false, ?_⟩
      have hy : edgeFun n k (by omega) y = false := only_hub hn
      have hu : Function.update (Fin.snoc y false : Fin (n+k+1) → Bool) (Fin.last (n+k)) true
          = Fin.snoc y true := Fin.update_snoc_last _ _ _
      simp only [Fin.snoc_last, Bool.not_false, hu, snoc_leaf, hy]
      simp [y]
    have hnc : ∃ x y : Fin (n+k) → Bool,
        edgeFun n (k+1) (by omega) (Fin.snoc x false) ≠
          edgeFun n (k+1) (by omega) (Fin.snoc y false) := by
      simpa [snoc_leaf] using (old_nonconstant (k := k) hn)
    have hbud : HasCircuitSize (n+k+1) (edgeFun n (k+1) (by omega)) (s-1+1) := by
      obtain ⟨C, hfan, hsize, hfun⟩ := h
      exact ⟨C, hfan, le_trans hsize (by omega), hfun⟩
    have held := L014 (n+k) (edgeFun n (k+1) (by omega)) false (s-1) hdep hnc hbud
    simp only [snoc_leaf, Bool.and_false, Bool.or_false] at held
    have := ih held
    omega

end Independent.PendantCycle
