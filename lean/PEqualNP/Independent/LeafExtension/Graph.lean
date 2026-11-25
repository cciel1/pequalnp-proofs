import Mathlib.Combinatorics.SimpleGraph.Operations
import PEqualNP.Defs.MetaComplexity
import PEqualNP.Defs.CoverPromise
import PEqualNP.Defs.PendantBit

/-! Attach fresh leaves to a finite simple graph. The first `n` labels are the
original vertices. Leaf `j` has label `n + j` and its sole neighbor is `a j`. -/

namespace Independent.LeafExtension

open SimpleGraph PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.CoverPromise (IsVertexCover)

variable {n : ℕ}

/-- Boolean edge function in the L105 circuit model. -/
def edgeFun (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) : Bool :=
  decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)

/-- Add one fresh vertex with one incident edge, at the specified old vertex. -/
def addLeaf (G : SimpleGraph (Fin n)) (v : Fin n) : SimpleGraph (Fin (n+1)) :=
  G.map Fin.castSuccEmb ⊔ SimpleGraph.edge v.castSucc (Fin.last n)

instance (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    DecidableRel (addLeaf G v).Adj := by unfold addLeaf; infer_instance

theorem addLeaf_adj (G : SimpleGraph (Fin n)) (v : Fin n) (i j : Fin (n+1)) :
    (addLeaf G v).Adj i j ↔
      (∃ p q, G.Adj p q ∧ p.castSucc = i ∧ q.castSucc = j) ∨
      (i = v.castSucc ∧ j = Fin.last n) ∨ (i = Fin.last n ∧ j = v.castSucc) := by
  rw [addLeaf, sup_adj, map_adj, edge_adj]
  simp only [Fin.coe_castSuccEmb]
  constructor
  · rintro (h | ⟨h, _⟩)
    exacts [Or.inl h, Or.inr h]
  · rintro (h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, Fin.castSucc_ne_last _⟩
    · exact Or.inr ⟨Or.inr ⟨rfl, rfl⟩, (Fin.castSucc_ne_last _).symm⟩

@[simp] theorem addLeaf_adj_old (G : SimpleGraph (Fin n)) (v i j : Fin n) :
    (addLeaf G v).Adj i.castSucc j.castSucc ↔ G.Adj i j := by
  simp [addLeaf_adj]

@[simp] theorem addLeaf_adj_last (G : SimpleGraph (Fin n)) (v : Fin n) (i : Fin (n+1)) :
    (addLeaf G v).Adj i (Fin.last n) ↔ i = v.castSucc := by
  simp [addLeaf_adj, Ne.symm (Fin.castSucc_ne_last v)]

private theorem card_congr {V : Type*} {G H : SimpleGraph V} {i : Fintype G.edgeSet}
    {j : Fintype H.edgeSet} (e : G = H) :
    (@SimpleGraph.edgeFinset V G i).card = (@SimpleGraph.edgeFinset V H j).card := by
  subst H
  cases Subsingleton.elim i j
  rfl

theorem addLeaf_card (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    (addLeaf G v).edgeFinset.card = G.edgeFinset.card + 1 := by
  have h := SimpleGraph.card_edgeFinset_sup_edge (G.map Fin.castSuccEmb)
    (s := v.castSucc) (t := Fin.last n) (by rw [map_adj]; simp) (Fin.castSucc_ne_last v)
  have hm := SimpleGraph.card_edgeFinset_map Fin.castSuccEmb G
  exact (card_congr (by rfl)).trans (h.trans (congrArg (· + 1) ((card_congr rfl).trans hm)))

/-- The recursive form preserves the order of inputs for last-wire elimination. -/
def attach (G : SimpleGraph (Fin n)) : (k : ℕ) → (Fin k → Fin n) → SimpleGraph (Fin (n+k))
  | 0, _ => G
  | k+1, a => addLeaf (attach G k (fun j => a j.castSucc)) (Fin.castAdd k (a (Fin.last k)))

instance attachDec (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (k : ℕ) → (a : Fin k → Fin n) → DecidableRel (attach G k a).Adj
  | 0, _ => inferInstanceAs (DecidableRel G.Adj)
  | k+1, a => by
    letI := attachDec G k (fun j => a j.castSucc)
    unfold attach
    infer_instance

variable {k : ℕ}

@[simp] theorem attach_adj_old (G : SimpleGraph (Fin n)) (a : Fin k → Fin n) (u v : Fin n) :
    (attach G k a).Adj (Fin.castAdd k u) (Fin.castAdd k v) ↔ G.Adj u v := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact (addLeaf_adj_old ..).trans (ih ..)

/-- This identifies the entire neighborhood, including the absence of leaf-leaf edges. -/
@[simp] theorem attach_adj_leaf (G : SimpleGraph (Fin n)) (a : Fin k → Fin n)
    (i : Fin (n+k)) (j : Fin k) :
    (attach G k a).Adj i (Fin.natAdd n j) ↔ i = Fin.castAdd k (a j) := by
  induction k with
  | zero => exact j.elim0
  | succ k ih =>
    refine Fin.lastCases ?_ (fun t => ?_) j
    · exact addLeaf_adj_last ..
    · refine Fin.lastCases ?_ (fun u => ?_) i
      · rw [SimpleGraph.adj_comm]
        change (addLeaf _ _).Adj (Fin.natAdd n t).castSucc (Fin.last (n+k)) ↔ _
        rw [addLeaf_adj_last]
        simp [Fin.ext_iff]
        omega
      · change (addLeaf _ _).Adj u.castSucc (Fin.natAdd n t).castSucc ↔
          u.castSucc = (Fin.castAdd k (a t.castSucc)).castSucc
        rw [addLeaf_adj_old, Fin.castSucc_inj]
        exact ih ..

theorem attach_card (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : Fin k → Fin n) :
    (attach G k a).edgeFinset.card = G.edgeFinset.card + k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h := addLeaf_card (attach G k (fun j => a j.castSucc)) (Fin.castAdd k (a (Fin.last k)))
    rw [ih] at h
    convert! h using 2

theorem attach_hasEdge (G : SimpleGraph (Fin n)) (a : Fin k → Fin n)
    (he : ∃ i j, G.Adj i j) : ∃ i j, (attach G k a).Adj i j := by
  obtain ⟨i,j,h⟩ := he
  exact ⟨_, _, (attach_adj_old G a i j).mpr h⟩

/-- Lifting an old cover covers the extension exactly when it contains every anchor. -/
theorem map_cover_iff (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) (a : Fin k → Fin n) :
    IsVertexCover (attach G k a) (T.map (Fin.castAddEmb k)) ↔
      IsVertexCover G T ∧ ∀ j, a j ∈ T := by
  have memOld (v : Fin n) : Fin.castAdd k v ∈ T.map (Fin.castAddEmb k) ↔ v ∈ T :=
    Finset.mem_map' _
  have notLeaf (j : Fin k) : Fin.natAdd n j ∉ T.map (Fin.castAddEmb k) := by
    rintro h
    obtain ⟨v, _, e⟩ := Finset.mem_map.mp h
    have := congrArg Fin.val e
    simp only [Fin.castAddEmb_apply, Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  constructor
  · intro h
    constructor
    · intro u v huv
      exact (h _ _ ((attach_adj_old G a u v).mpr huv)).imp (memOld _).mp (memOld _).mp
    · intro j
      exact (memOld _).mp ((h _ _ ((attach_adj_leaf G a _ j).mpr rfl)).resolve_right (notLeaf j))
  · rintro ⟨hT, ha⟩
    intro i j
    refine Fin.addCases (fun u => ?_) (fun l => ?_) i
    · refine Fin.addCases (fun v => ?_) (fun l => ?_) j
      · intro huv
        exact (hT _ _ ((attach_adj_old ..).mp huv)).imp (memOld _).mpr (memOld _).mpr
      · intro h
        exact Or.inl ((attach_adj_leaf ..).mp h ▸ (memOld _).mpr (ha l))
    · intro h
      exact Or.inr ((attach_adj_leaf G a _ l).mp h.symm ▸ (memOld _).mpr (ha l))

/-- Exact agreement with the project's pendant Boolean function, with no graph premises. -/
theorem edgeFun_addLeaf (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    edgeFun (addLeaf G v) = PEqualNP.PendantBit.pendF n (edgeFun G) v := by
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [edgeFun, PEqualNP.PendantBit.pendF, decide_eq_true_iff, Bool.or_eq_true,
    Bool.and_eq_true]
  constructor
  · rintro ⟨i,j,h,hi,hj⟩
    rcases (addLeaf_adj ..).mp h with ⟨p,q,hpq,rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    exacts [Or.inl ⟨p,q,hpq,hi,hj⟩, Or.inr ⟨hi,hj⟩, Or.inr ⟨hj,hi⟩]
  · rintro (⟨i,j,h,hi,hj⟩ | ⟨hv,hl⟩)
    · exact ⟨_, _, (addLeaf_adj_old G v i j).mpr h, hi, hj⟩
    · exact ⟨_, _, (addLeaf_adj_last G v _).mpr rfl, hv, hl⟩

end Independent.LeafExtension
