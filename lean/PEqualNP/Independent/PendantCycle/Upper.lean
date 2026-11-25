import PEqualNP.Independent.PendantCycle.Basic
import PEqualNP.MetaComplexity.Helpers.CycleUpper

namespace Independent.PendantCycle

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.PathSize PEqualNP.MetaComplexity.Helpers.CycleSize
open PEqualNP.MetaComplexity.Helpers.CycleSize.PG

/-- Append one OR per listed input to the value on `seed`. -/
private theorem orChain (width seed : ℕ) (hseed : seed < width) (xs : List ℕ)
    (hxs : ∀ i ∈ xs, i < width) :
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length = xs.length ∧
      out < width + gs.length ∧ ∀ w : List Bool, w.length = width →
      (wiresFrom gs w).getD out false =
        (w.getD seed false || xs.any (fun i => w.getD i false)) := by
  induction xs with
  | nil => exact ⟨[], seed, by simp, rfl, by simpa, by simp [wiresFrom]⟩
  | cons i xs ih =>
    obtain ⟨gs, out, ok, len, ho, ev⟩ := ih (fun j hj => hxs j (by simp [hj]))
    refine ⟨gs ++ [⟨.or, [i, out]⟩], width + gs.length, ?_, by simp [len], by simp, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact ok g hg
      · simpa using List.mem_singleton.mp hg ▸ (show Ok (⟨.or, [i, out]⟩ : Gate) by simp [Ok])
    · intro w hw
      let v := wiresFrom gs w
      have lv : v.length = width + gs.length := by simp [v, length_wiresFrom, hw]
      have ei : v.getD i false = w.getD i false := getD_wiresFrom _ _ _ (by rw [hw]; exact hxs i (by simp))
      have eo : v.getD out false = _ := ev w hw
      rw [wiresFrom_append, ← lv]
      change (v ++ [GateOp.or.eval ([i,out].map fun j => v.getD j false)]).getD v.length false = _
      rw [getD_snoc_eq]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq, ei, eo, Bool.or_left_comm]

/-- The two gates joining the path output with the star at the last cycle vertex. -/
private theorem finish (w : List Bool) (path center neighbours : ℕ) (hp : path < w.length) :
    (wiresFrom [⟨.and, [center, neighbours]⟩, ⟨.or, [path, w.length]⟩] w).getD
      (w.length + 1) false = (w.getD path false || (w.getD center false && w.getD neighbours false)) := by
  have eq : ∀ (t : List Bool), (w ++ t)[path]?.getD false = w[path]?.getD false := by
    intro t; rw [List.getElem?_append_left hp]
  simp [wiresFrom, GateOp.eval, eq]

private def leafIndices (n k : ℕ) : List ℕ :=
  List.ofFn (fun j : Fin k => n + j.val)

private theorem leafIndices_lt (n k i : ℕ) (hi : i ∈ leafIndices n k) : i < n + k := by
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
  exact Nat.add_lt_add_left j.isLt n

private theorem input_at {N : ℕ} (x : Fin N → Bool) (i : ℕ) (hi : i < N) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  rw [getD_ofFn_ext, ext, dite_eq_left hi]

/-- Split the function into the path on the first `m` vertices and the star at vertex `m`. -/
private theorem path_or_star (m k : ℕ) (hm : 2 ≤ m) (x : Fin (m+1+k) → Bool) :
    edgeFun (m+1) k (by omega) x =
    (pathB (List.ofFn x) m || ((List.ofFn x).getD m false &&
      ((List.ofFn x).getD (m-1) false ||
        (0 :: leafIndices (m+1) k).any (fun i => (List.ofFn x).getD i false)))) := by
  let y : Fin (m + 1) → Bool := fun i => x (Fin.castAdd k i)
  have path_eq : pathB (List.ofFn y) m = pathB (List.ofFn x) m := by
    rw [Bool.eq_iff_iff, pathB_iff, pathB_iff]
    constructor <;> rintro ⟨i, hi, e, e'⟩ <;> refine ⟨i, hi, ?_, ?_⟩
    all_goals simp only [input_at _ _ (show i < m+1 by omega), input_at _ _ (show i+1 < m+1 by omega),
      input_at _ _ (show i < m+1+k by omega), input_at _ _ (show i+1 < m+1+k by omega)] at *
    all_goals assumption
  have leaves : (leafIndices (m+1) k).any (fun i => (List.ofFn x).getD i false) =
      decide (∃ j : Fin k, x (Fin.natAdd (m+1) j) = true) := by
    rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
    constructor
    · rintro ⟨_, hi, hv⟩
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
      rw [input_at _ _ (Nat.add_lt_add_left j.isLt _)] at hv
      exact ⟨j, hv⟩
    · rintro ⟨j, hj⟩
      exact ⟨m+1+j.val, List.mem_ofFn.mpr ⟨j,rfl⟩, by rw [input_at _ _ (Nat.add_lt_add_left j.isLt _)]; exact hj⟩
  change (cyc (m+1) y || (x _ && _)) = _
  rw [cyc_eq_path_or m hm, path_eq, List.any_cons, leaves, input_at _ m (by omega),
    input_at _ (m-1) (by omega), input_at _ 0 (by omega)]
  simp only [ext, dite_eq_left (show m < m+1 by omega), dite_eq_left (show m-1 < m+1 by omega),
    dite_eq_left (show 0 < m+1 by omega), y, Nat.add_sub_cancel]
  have regroup (p c a b l : Bool) :
      ((p || (c && (a || b))) || (c && l)) = (p || (c && (a || (b || l)))) := by
    decide +revert
  exact regroup _ _ _ _ _

/-- Compute the path first, then OR the two cyclic neighbours and all leaves of the centre. -/
theorem upper {n k s : ℕ} (hn : 5 ≤ n) (hs : n + (n+1)/2 + k ≤ s+1) :
    HasCircuitSize (n+k) (edgeFun n k (by omega)) s := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m+1 := ⟨n-1, by omega⟩
  let width := m+1+k
  obtain ⟨gs, path, ok, len, hp, ev⟩ := pathGates m (by omega) width (by dsimp [width]; omega)
  let xs := 0 :: leafIndices (m+1) k
  have hxs : ∀ i ∈ xs, i < width := by
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · dsimp [width]; omega
    · exact leafIndices_lt _ _ _ hi
  obtain ⟨os, neighbours, ok', len', ho, ev'⟩ := orChain (width + gs.length) (m-1)
    (by dsimp [width]; omega) xs (fun i hi => by have := hxs i hi; omega)
  let last := width + gs.length + os.length
  refine ⟨⟨(gs ++ os) ++ [⟨.and, [m, neighbours]⟩, ⟨.or, [path, last]⟩], last+1⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with (hg | hg) | (rfl | rfl)
    · exact ok g hg
    · exact ok' g hg
    · simp
    · simp
  · have lxs : xs.length = k+1 := by simp [xs, leafIndices]
    simp only [Circuit.size, List.length_append, List.length_cons, List.length_nil]
    omega
  · intro x
    let w := List.ofFn x
    let v := wiresFrom gs w
    let u := wiresFrom os v
    have lw : w.length = width := by simp [w, width]
    have lv : v.length = width + gs.length := by simp [v, length_wiresFrom, lw]
    have lu : u.length = last := by simp [u, last, length_wiresFrom, lv]
    have vi (i : ℕ) (hi : i < width) : v.getD i false = w.getD i false :=
      getD_wiresFrom _ _ _ (by omega)
    have ei (i : ℕ) (hi : i < v.length) : u.getD i false = v.getD i false :=
      getD_wiresFrom _ _ _ hi
    have epath : u.getD path false = pathB w m := (ei path (by omega)).trans (ev w lw)
    have ec : u.getD m false = w.getD m false := by
      have h : m < width := by dsimp [width]; omega
      rw [ei _ (by omega), vi _ h]
    have en : u.getD neighbours false = (w.getD (m-1) false || xs.any (fun i => w.getD i false)) := by
      change (wiresFrom os v).getD neighbours false = _
      rw [ev' v lv, vi _ (by dsimp [width]; omega)]
      congr 1
      rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
      constructor <;> rintro ⟨i, hi, e⟩ <;> refine ⟨i, hi, ?_⟩
      · rwa [vi i (hxs i hi)] at e
      · rwa [vi i (hxs i hi)]
    simp only [Circuit.eval, wires_eq, wiresFrom_append]
    change (wiresFrom [⟨.and, [m, neighbours]⟩, ⟨.or, [path, last]⟩] u).getD (last+1) false = _
    rw [← lu, finish _ _ _ _ (by dsimp [last] at lu; omega), epath, ec, en,
      path_or_star _ _ (by omega) x]

end Independent.PendantCycle
