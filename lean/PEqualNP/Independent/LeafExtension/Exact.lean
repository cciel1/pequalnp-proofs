import PEqualNP.Independent.LeafExtension.Lower
import PEqualNP.Independent.LeafExtension.Cover
import PEqualNP.MetaComplexity.L105

/-! The unrestricted lower bound charges one gate for each new input. The
matching upper bound uses the lifted old cover on the explicit extended graph. -/

namespace Independent.LeafExtension

open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.CoverPromise (IsVertexCover)
open PEqualNP.PendantBit (minCircuitSize)

variable {n k s : ℕ}

private theorem budget_mono {f : (Fin n → Bool) → Bool} {u v : ℕ}
    (h : HasCircuitSize n f u) (huv : u ≤ v) : HasCircuitSize n f v := by
  obtain ⟨C,hf,hs,he⟩ := h
  exact ⟨C, hf, hs.trans huv, he⟩

/-- Even without base optimality, the constrained cover yields this upper bound. -/
theorem upper (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (a : Fin k → Fin n) (he : ∃ i j, G.Adj i j) (hT : IsVertexCover G T)
    (ha : ∀ j, a j ∈ T) :
    HasCircuitSize (n+k) (edgeFun (attach G k a)) (G.edgeFinset.card + T.card - 1 + k) := by
  have hE : 0 < G.edgeFinset.card := by
    obtain ⟨i,j,hij⟩ := he
    exact Finset.card_pos.mpr ⟨s(i,j), SimpleGraph.mem_edgeFinset.mpr hij⟩
  have h := L105 (n+k) (attach G k a) (T.map (Fin.castAddEmb k)) (attach_hasEdge G a he)
    ((map_cover_iff G T a).mpr ⟨hT,ha⟩)
  rw [attach_card, Finset.card_map] at h
  exact budget_mono h (by omega)

/-- A cover attaining the base circuit minimum remains exact after any finite
sequence of leaves anchored in that cover. Only a base-graph size equality is assumed. -/
theorem exact_size (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (a : Fin k → Fin n) (he : ∃ i j, G.Adj i j) (hT : IsVertexCover G T)
    (ha : ∀ j, a j ∈ T)
    (htight : minCircuitSize n (edgeFun G) = G.edgeFinset.card + T.card - 1) :
    HasCircuitSize (n+k) (edgeFun (attach G k a)) s ↔
      G.edgeFinset.card + T.card - 1 + k ≤ s := by
  constructor
  · intro h
    obtain ⟨t, ht, hts⟩ := eliminate_leaves G a he h
    have hb : minCircuitSize n (edgeFun G) ≤ t := Nat.sInf_le ht
    omega
  · exact budget_mono (upper G T a he hT ha)

/-- A budget characterization determines the infimum and supplies its witness. -/
theorem minimum_of_budget_iff {m z : ℕ} {f : (Fin m → Bool) → Bool}
    (h : ∀ s, HasCircuitSize m f s ↔ z ≤ s) : minCircuitSize m f = z := by
  apply IsLeast.csInf_eq
  exact ⟨(h z).mpr le_rfl, fun s hs => (h s).mp hs⟩

theorem min_size_attach (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (a : Fin k → Fin n) (he : ∃ i j, G.Adj i j) (hT : IsVertexCover G T)
    (ha : ∀ j, a j ∈ T)
    (htight : minCircuitSize n (edgeFun G) = G.edgeFinset.card + T.card - 1) :
    minCircuitSize (n+k) (edgeFun (attach G k a)) = minCircuitSize n (edgeFun G) + k := by
  rw [htight]
  exact minimum_of_budget_iff (fun _ => exact_size G T a he hT ha htight)

end Independent.LeafExtension
