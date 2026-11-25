import PEqualNP.Independent.LeafExtension.Graph

namespace Independent.LeafExtension

open PEqualNP.MetaComplexity.CoverPromise (IsVertexCover)

variable {n k : ℕ}

/-- Replace every selected leaf by its anchor. This operation can only shrink a cover. -/
def retractCover (a : Fin k → Fin n) (U : Finset (Fin (n+k))) : Finset (Fin n) :=
  U.image (Fin.addCases id a)

theorem retractCover_card_le (a : Fin k → Fin n) (U : Finset (Fin (n+k))) :
    (retractCover a U).card ≤ U.card := Finset.card_image_le

theorem retractCover_spec (G : SimpleGraph (Fin n)) (a : Fin k → Fin n)
    (U : Finset (Fin (n+k))) (hU : IsVertexCover (attach G k a) U) :
    IsVertexCover G (retractCover a U) ∧ ∀ j, a j ∈ retractCover a U := by
  have old (u : Fin n) (hu : Fin.castAdd k u ∈ U) : u ∈ retractCover a U :=
    Finset.mem_image.mpr ⟨_, hu, Fin.addCases_left ..⟩
  constructor
  · intro u v huv
    exact (hU _ _ ((attach_adj_old G a u v).mpr huv)).imp (old u) (old v)
  · intro j
    rcases hU _ _ ((attach_adj_leaf G a _ j).mpr rfl) with h | h
    · exact old _ h
    · exact Finset.mem_image.mpr ⟨_, h, Fin.addCases_right ..⟩

/-- The vertex cover number of the extension is the minimum size of an old
vertex cover containing all the anchors. This statement avoids any choice of
minimizer, and the cardinality of repeated anchors is never overcounted. -/
theorem cover_budget_iff (G : SimpleGraph (Fin n)) (a : Fin k → Fin n) (b : ℕ) :
    (∃ U, IsVertexCover (attach G k a) U ∧ U.card ≤ b) ↔
      ∃ T, IsVertexCover G T ∧ (∀ j, a j ∈ T) ∧ T.card ≤ b := by
  constructor
  · rintro ⟨U,hU,hub⟩
    obtain ⟨hT,ha⟩ := retractCover_spec G a U hU
    exact ⟨_, hT, ha, (retractCover_card_le a U).trans hub⟩
  · rintro ⟨T,hT,ha,htb⟩
    exact ⟨_, (map_cover_iff G T a).mpr ⟨hT,ha⟩, by simpa using htb⟩

end Independent.LeafExtension
