import BoundaryCount

namespace FanoMixedSize
open FanoBoundary

private instance localIncDec : DecidableRel incident := fun p l =>
  inferInstanceAs (Decidable (p = l ∨ p = l + 1 ∨ p = l + 3))

/-- All raw points lying on the line in the incidence relation used by the task. -/
def neighborhood (l : Fin 7) : Finset (Fin 7) := Finset.univ.filter fun p => incident p l

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem saturated_shape : ∀ S : Finset (Fin 7), (supportedFlags S).card = 3 →
    (∃ p, S = {p}) ∨ (∃ l, S = neighborhood l) := by decide +kernel

private theorem flag_singleton : ∀ p q l : Fin 7,
    (p,l) ∈ supportedFlags {q} ↔ p = q ∧ incident p l := by decide +kernel

private theorem flag_neighborhood : ∀ p l t : Fin 7,
    (p,l) ∈ supportedFlags (neighborhood t) ↔ l = t ∧ incident p l := by decide +kernel

private theorem distinct_shapes : ∀ p l : Fin 7, ({p} : Finset (Fin 7)) ≠ neighborhood l := by decide

private theorem meet : ∀ p q : Fin 7, ∃ l, incident p l ∧ incident q l := by decide

/-- With seven features the twenty-one flags have exactly one provider and every provider
uses all three available slots. -/
theorem seven_flag_partition (S : Fin 7 → Finset (Fin 7))
    (cover : flagSet ⊆ Finset.univ.biUnion (fun i => supportedFlags (S i))) :
    (∀ i, (supportedFlags (S i)).card = 3) ∧
    ∀ i j e, e ∈ supportedFlags (S i) → e ∈ supportedFlags (S j) → i = j := by
  classical
  let D := (i : Fin 7) × ↥(supportedFlags (S i))
  let π : D → ↥flagSet := fun x => ⟨x.2.val, (Finset.mem_filter.mp x.2.property).1⟩
  have onto : Function.Surjective π := by
    intro e
    obtain ⟨i, _, h⟩ := Finset.mem_biUnion.mp (cover e.property)
    exact ⟨⟨i, ⟨e.val, h⟩⟩, rfl⟩
  have hsum : ∑ i, (supportedFlags (S i)).card ≤ ∑ _i : Fin 7, 3 :=
    Finset.sum_le_sum fun i _ => flag_cap (S i)
  have count : Fintype.card D = ∑ i, (supportedFlags (S i)).card := by simp [D, Fintype.card_sigma]
  have nflags : Fintype.card ↥flagSet = 21 := by simpa using flagSet_card
  have same : Fintype.card D = Fintype.card ↥flagSet := by
    have bot := Fintype.card_le_of_surjective π onto
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    omega
  have inj := ((Fintype.bijective_iff_surjective_and_card π).mpr ⟨onto, same⟩).1
  constructor
  · have heq : ∑ i, (supportedFlags (S i)).card = ∑ _i : Fin 7, 3 := by
      rw [← count, same, nflags]
      decide
    exact fun i => (Finset.sum_eq_sum_iff_of_le (fun i _ => flag_cap (S i))).mp heq i (Finset.mem_univ _)
  · intro i j e hi hj
    exact congrArg Sigma.fst (inj (a₁ := ⟨i, ⟨e,hi⟩⟩) (a₂ := ⟨j, ⟨e,hj⟩⟩) rfl)

/-- Equality forces a complete point-centered or complete line-centered cover. -/
theorem seven_rigidity (S : Fin 7 → Finset (Fin 7))
    (cover : flagSet ⊆ Finset.univ.biUnion (fun i => supportedFlags (S i))) :
    (∀ i, ∃ p, S i = {p}) ∨ (∀ i, ∃ l, S i = neighborhood l) := by
  classical
  obtain ⟨sat, uniq⟩ := seven_flag_partition S cover
  have shape (i : Fin 7) := saturated_shape (S i) (sat i)
  have clash (i j p l : Fin 7) (hi : S i = {p}) (hj : S j = neighborhood l)
      (inc : incident p l) : False := by
    have hs : (p,l) ∈ supportedFlags (S i) := hi ▸ (flag_singleton p p l).mpr ⟨rfl, inc⟩
    have hn : (p,l) ∈ supportedFlags (S j) := hj ▸ (flag_neighborhood p l l).mpr ⟨rfl, inc⟩
    have eq := uniq i j _ hs hn
    subst j
    exact distinct_shapes p l (hi.symm.trans hj)
  by_cases sing : ∃ i p, S i = {p}
  · obtain ⟨i,p,hi⟩ := sing
    left
    intro j
    rcases shape j with s | ⟨t,hj⟩
    · exact s
    · exfalso
      have itt : incident t t := Or.inl rfl
      obtain ⟨m, hpm, htm⟩ := meet p t
      have hf : (t,m) ∈ flagSet := Finset.mem_filter.mpr ⟨Finset.mem_univ _, htm⟩
      obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp (cover hf)
      rcases shape k with ⟨q,hq⟩ | ⟨u,hu⟩
      · rw [hq] at hk
        have e := ((flag_singleton t q m).mp hk).1
        exact clash k j t t (e ▸ hq) hj itt
      · rw [hu] at hk
        have e := ((flag_neighborhood t m u).mp hk).1
        exact clash i k p m hi (e ▸ hu) hpm
  · right
    intro i
    exact (shape i).resolve_left (fun ⟨p,h⟩ => sing ⟨i,p,h⟩)

/-- Every center occurs exactly once, so equality is rigid up to permutation of the inputs. -/
theorem seven_rigidity_perm (S : Fin 7 → Finset (Fin 7))
    (cover : flagSet ⊆ Finset.univ.biUnion (fun i => supportedFlags (S i))) :
    (∃ e : Equiv.Perm (Fin 7), ∀ i, S i = {e i}) ∨
      (∃ e : Equiv.Perm (Fin 7), ∀ i, S i = neighborhood (e i)) := by
  classical
  obtain ⟨sat, uniq⟩ := seven_flag_partition S cover
  have inj : Function.Injective S := by
    intro i j eq
    obtain ⟨f,hf⟩ := Finset.card_pos.mp (show 0 < (supportedFlags (S i)).card by rw [sat]; decide)
    exact uniq i j f hf (eq ▸ hf)
  have perm (centers : Fin 7 → Finset (Fin 7)) (shape : ∀ i, ∃ c, S i = centers c) :
      ∃ e : Equiv.Perm (Fin 7), ∀ i, S i = centers (e i) := by
    choose c hc using shape
    have hcInj : Function.Injective c := fun i j eq => inj (by rw [hc i, hc j, eq])
    exact ⟨Equiv.ofBijective c hcInj.bijective_of_finite, hc⟩
  exact (seven_rigidity S cover).imp (perm fun p => {p}) (perm neighborhood)

/-- For a decomposition computing incidence with seven point-side features, their singleton
supports are either all the points or all the lines, in an arbitrary input order. -/
theorem seven_point_feature_rigidity {b : Nat}
    (P : Fin 7 → Input (Fin 7) → Bool) (L : Fin b → Input (Fin 7) → Bool)
    (hP : ∀ i, MonotoneFeature (P i)) (M : Input (Fin 7) → Input (Fin b) → Bool)
    (hm : MixedMono M) (computes : ∀ x y, M (fun i => P i x) (fun j => L j y) = true ↔
      AcceptsEdge incident x y) :
    (∃ e : Equiv.Perm (Fin 7), ∀ i, pointSignature P i = {e i}) ∨
      (∃ e : Equiv.Perm (Fin 7), ∀ i, pointSignature P i = neighborhood (e i)) :=
  seven_rigidity_perm (pointSignature P) (flag_coverage P L hP M hm computes)

#print axioms seven_rigidity_perm
#print axioms seven_point_feature_rigidity
end FanoMixedSize
