import WireFacts

namespace FanoPureTriples
open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open FanoWireFacts

abbrev Input := Fin 7 → Bool
def incident (p l : Fin 7) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3
instance : DecidableRel incident := fun p l =>
  inferInstanceAs (Decidable (p = l ∨ p = l + 1 ∨ p = l + 3))
def one (p : Fin 7) : Input := fun q => decide (q = p)
def outside (l : Fin 7) : Input := fun p => decide (¬ incident p l)
abbrev V (C : Circuit) (w : ℕ) (x : Input) := BlindGate.wireValue C 7 x w = true

private theorem split_gate {C : Circuit} (h : TopForm.IsAO2 7 C) {w : ℕ}
    (lo : 7 ≤ w) (hi : w < 7+C.size) :
    ∃ a < w, ∃ b < w, (∀ x, V C w x ↔ V C a x ∧ V C b x) ∨
                        (∀ x, V C w x ↔ V C a x ∨ V C b x) := by
  obtain ⟨j, rfl⟩ : ∃ j, w = 7 + j := ⟨w-7, by omega⟩
  have hj : j < C.gates.length := by change 7+j < 7+C.gates.length at hi; omega
  obtain ⟨hao, hrb, hlen⟩ := h
  have hgm := List.getElem_mem hj
  have hl := hlen _ hgm
  obtain ⟨a,b,hab⟩ : ∃ a b, C.gates[j].inputs = [a,b] := by
    rcases hq : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c,t⟩⟩⟩
    · simp [hq] at hl
    · simp [hq] at hl
    · exact ⟨a,b,rfl⟩
    · simp [hq] at hl
  have earlier (i : Nat) (hi : i ∈ [a,b]) : i < 7+j := by
    apply hrb j hj i
    rwa [gateAt_eq hj, hab]
  refine ⟨a, earlier a (by simp), b, earlier b (by simp), ?_⟩
  rcases hao _ hgm with hand | hor
  · left; intro x; unfold V; rw [wv_gate C hrb x j hj, hab, hand]; simp [GateOp.eval]
  · right; intro x; unfold V; rw [wv_gate C hrb x j hj, hab, hor]; simp [GateOp.eval]

private theorem wire_mono {C : Circuit} (h : TopForm.IsAO2 7 C) (w : ℕ)
    (x y : Input) (hxy : ∀ i, x i = true → y i = true) : V C w x → V C w y := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases lo : w < 7
    · unfold V; rw [wv_input C x w lo, wv_input C y w lo]; exact hxy _
    by_cases hi : w < 7+C.size
    · obtain ⟨a, ha, b, hb, hand | hor⟩ := split_gate h (by omega) hi
      · rw [hand,hand]; exact And.imp (ih a ha) (ih b hb)
      · rw [hor,hor]; exact Or.imp (ih a ha) (ih b hb)
    · intro hx; unfold V at hx
      rw [wv_ge C x w (by change 7+C.size ≤ w; omega)] at hx
      contradiction

private theorem geometry : ∀ p q l t : Fin 7, p ≠ q →
    incident p l → incident q l → incident p t → incident q t → l = t := by decide +kernel

private theorem different : ∀ l : Fin 7, l ≠ l+1 ∧ l ≠ l+3 ∧ l+1 ≠ l+3 := by decide

/-- A counted wire accepts two singleton inputs and rejects the whole complement. -/
def Good (C : Circuit) (l : Fin 7) (w : ℕ) : Prop :=
  (¬ V C w (outside l)) ∧ ∃ p q : Fin 7, p ≠ q ∧ V C w (one p) ∧ V C w (one q)

def Full (C : Circuit) (l : Fin 7) (w : ℕ) : Prop :=
  (¬ V C w (outside l)) ∧ ∀ p, incident p l → V C w (one p)

private theorem full_good {C l w} (h : Full C l w) : Good C l w :=
  ⟨h.1,l,l+1,(different l).1,h.2 l (Or.inl rfl),h.2 (l+1) (Or.inr (Or.inl rfl))⟩

private theorem good_range {C l w} (h : Good C l w) : 7 ≤ w ∧ w < 7+C.size := by
  obtain ⟨_,p,q,hpq,hp,hq⟩ := h
  constructor
  · by_contra! h
    unfold V at hp hq
    rw [wv_input C (one p) w h] at hp
    rw [wv_input C (one q) w h] at hq
    have h1 : (⟨w,h⟩ : Fin 7) = p := of_decide_eq_true hp
    have h2 : (⟨w,h⟩ : Fin 7) = q := of_decide_eq_true hq
    exact hpq (h1.symm.trans h2)
  · by_contra! h
    unfold V at hp
    rw [wv_ge C (one p) w h] at hp
    contradiction

private theorem unique_line {C : Circuit} (hAO : TopForm.IsAO2 7 C)
    {l t : Fin 7} {w : Nat} (hl : Good C l w) (ht : Good C t w) : l = t := by
  obtain ⟨p,q,neq,hp,hq⟩ := hl.2
  have inside (s v : Fin 7) (hs : ¬ V C w (outside s)) (hv : V C w (one v)) : incident v s := by
    by_contra hn
    apply hs (wire_mono hAO w (one v) (outside s) ?_ hv)
    intro i h1
    have e : i = v := of_decide_eq_true h1
    subst i
    simpa [outside] using hn
  exact geometry p q l t neq (inside l p hl.1 hp) (inside l q hl.1 hq)
    (inside t p ht.1 hp) (inside t q ht.1 hq)

private theorem two_color {P Q : Fin 7 → Prop} (l : Fin 7)
    (covers : ∀ p, incident p l → P p ∨ Q p) :
    (∃ p q, p ≠ q ∧ P p ∧ P q) ∨ (∃ p q, p ≠ q ∧ Q p ∧ Q q) := by
  obtain ⟨h01,h03,h13⟩ := different l
  rcases covers l (Or.inl rfl) with a|a <;>
    rcases covers (l+1) (Or.inr (Or.inl rfl)) with b|b <;>
    rcases covers (l+3) (Or.inr (Or.inr rfl)) with c|c
  all_goals first
    | exact Or.inl ⟨_,_,h01,a,b⟩
    | exact Or.inl ⟨_,_,h03,a,c⟩
    | exact Or.inl ⟨_,_,h13,b,c⟩
    | exact Or.inr ⟨_,_,h01,a,b⟩
    | exact Or.inr ⟨_,_,h03,a,c⟩
    | exact Or.inr ⟨_,_,h13,b,c⟩

/-- A full line requires two distinct counted gate wires. -/
theorem two_gates {C : Circuit} (hAO : TopForm.IsAO2 7 C) (l : Fin 7)
    (h : ∃ w, Full C l w) : ∃ a b, a < b ∧ Good C l a ∧ Good C l b := by
  classical
  let w := Nat.find h
  have hw : Full C l w := Nat.find_spec h
  have small : ∀ t < w, ¬ Full C l t := fun t ht => Nat.find_min h ht
  have gw := full_good hw
  obtain ⟨lo,hi⟩ := good_range gw
  obtain ⟨a,ha,b,hb,hand|hor⟩ := split_gate hAO lo hi
  · exfalso
    have both (p) (hpl : incident p l) := (hand (one p)).mp (hw.2 p hpl)
    by_cases hsa : V C a (outside l)
    · exact small b hb ⟨fun hsb => hw.1 ((hand _).mpr ⟨hsa,hsb⟩),fun p hp => (both p hp).2⟩
    · exact small a ha ⟨hsa,fun p hp => (both p hp).1⟩
  · have cov (p) (hp : incident p l) := (hor (one p)).mp (hw.2 p hp)
    rcases two_color l cov with pair | pair
    · exact ⟨a,w,ha,⟨fun hx => hw.1 ((hor _).mpr (Or.inl hx)),pair⟩,gw⟩
    · exact ⟨b,w,hb,⟨fun hx => hw.1 ((hor _).mpr (Or.inr hx)),pair⟩,gw⟩

/-- Seven boundary tests imply fourteen distinct gates of the actual project circuit. -/
theorem boundary_floor {C : Circuit} (hAO : TopForm.IsAO2 7 C)
    (full : ∀ l, ∃ w, Full C l w) : 14 ≤ C.size := by
  classical
  choose a b hab ga gb using fun l => two_gates hAO l (full l)
  let f : Fin 7 × Bool → Fin C.size := fun ⟨l,k⟩ =>
    if k then ⟨b l-7, by have := good_range (gb l); omega⟩
    else ⟨a l-7, by have := good_range (ga l); omega⟩
  have spec (l : Fin 7) (k : Bool) : Good C l (7+(f (l,k)).val) := by
    cases k with
    | false => simpa [f, Nat.add_sub_of_le (good_range (ga l)).1] using ga l
    | true => simpa [f, Nat.add_sub_of_le (good_range (gb l)).1] using gb l
  have inj : Function.Injective f := by
    rintro ⟨l,i⟩ ⟨t,j⟩ hij
    have gi := spec l i
    have gj := spec t j
    rw [hij] at gi
    obtain rfl := unique_line hAO gi gj
    have hval := congrArg Fin.val hij
    have la := (good_range (ga l)).1
    have lb := (good_range (gb l)).1
    have lt := hab l
    cases i <;> cases j
    · rfl
    · change a l - 7 = b l - 7 at hval
      exfalso
      omega
    · change b l - 7 = a l - 7 at hval
      exfalso
      omega
    · rfl
  simpa using Fintype.card_le_of_injective f inj

/-- Multi-output floor when the selected wires compute the exact seven neighborhood ORs. -/
theorem exact_floor {C : Circuit} (hAO : TopForm.IsAO2 7 C) (w : Fin 7 → ℕ)
    (eqn : ∀ l x, V C (w l) x ↔ ∃ p, incident p l ∧ x p = true) : 14 ≤ C.size := by
  apply boundary_floor hAO
  intro l
  refine ⟨w l, fun ht => ?_, fun p hp => (eqn l _).mpr ⟨p,hp,by simp [one]⟩⟩
  obtain ⟨p,hp,hout⟩ := (eqn l _).mp ht
  exact (of_decide_eq_true hout) hp

#print axioms boundary_floor
#print axioms exact_floor
end FanoPureTriples
