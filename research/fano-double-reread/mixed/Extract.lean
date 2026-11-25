import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.Support

namespace MixedExtract
open PEqualNP.CircuitLowerBounds

def gateValue (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun j => w.getD j false)
def step (w : List Bool) (g : Gate) := w ++ [gateValue w g]
def renameGate (r : Nat → Nat) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩
def put (r : Nat → Nat) (i a j : Nat) := if j = i then a else r j

/-- Kept gates keep their operator and operand order. A cut gate's wire maps directly
to a primary input selected by boundary. The output map records every processed wire. -/
def compile (keep : Nat → Bool) (boundary : Nat → Nat) (i m : Nat)
    (r : Nat → Nat) (gs : List Gate) : List Gate × (Nat → Nat) :=
  match gs with
  | [] => ([], r)
  | g :: rest =>
    if keep i then
      let s := compile keep boundary (i+1) (m+1) (put r i m) rest
      (renameGate r g :: s.1, s.2)
    else compile keep boundary (i+1) m (put r i (boundary i)) rest

def countFrom (k : Nat → Bool) (i : Nat) : List Gate → Nat
  | [] => 0
  | _ :: gs => (if k i then 1 else 0) + countFrom k (i+1) gs

theorem length_compile (k d : _) (gs : List Gate) (i m : Nat) (r : Nat → Nat) :
    (compile k d i m r gs).1.length = countFrom k i gs := by
  induction gs generalizing i m r with
  | nil => rfl
  | cons g gs ih => cases h : k i <;> simp [compile, countFrom, h, ih, Nat.add_comm]

def extract (C : Circuit) (n m : Nat) (keep : Nat → Bool)
    (boundary : Nat → Nat) : Circuit :=
  let p := compile keep boundary n m boundary C.gates
  ⟨p.1, p.2 C.output⟩

theorem size_extract (C : Circuit) (n m : Nat) (keep : Nat → Bool) (d : Nat → Nat) :
    (extract C n m keep d).size = countFrom keep n C.gates := length_compile .. 

private theorem read_append {w : List Bool} (b : Bool) {j : Nat} (h : j < w.length) :
    (w ++ [b]).getD j false = w.getD j false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem read_last (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

/-- Evaluate an omitted gate on the actual old trace, and demand that its chosen primary
port gives that value. This can be applied separately to any collection of assignments. -/
def CutValues (k : Nat → Bool) (d : Nat → Nat) (b w : List Bool) : List Gate → Prop
  | [] => True
  | g :: gs =>
      (k w.length = false → d w.length < b.length ∧
        b.getD (d w.length) false = gateValue w g) ∧
      CutValues k d b (step w g) gs

def Back (i : Nat) : List Gate → Prop
  | [] => True
  | g :: gs => (∀ j ∈ g.inputs, j < i) ∧ Back (i+1) gs

def Prefix (b v : List Bool) : Prop :=
  b.length ≤ v.length ∧ ∀ j < b.length, v.getD j false = b.getD j false

def Maps (w v : List Bool) (r : Nat → Nat) : Prop :=
  ∀ j < w.length, r j < v.length ∧ v.getD (r j) false = w.getD j false

theorem simulate (k : Nat → Bool) (d : Nat → Nat) (b : List Bool) (gs : List Gate)
    (w v : List Bool) (r : Nat → Nat)
    (hp : Prefix b v) (hm : Maps w v r) (hb : Back w.length gs)
    (hc : CutValues k d b w gs) :
    let p := compile k d w.length v.length r gs
    Maps (gs.foldl step w) (p.1.foldl step v) p.2 := by
  induction gs generalizing w v r with
  | nil => exact hm
  | cons g gs ih =>
    obtain ⟨hback, hback'⟩ := hb
    obtain ⟨hcut, hcut'⟩ := hc
    have len : (step w g).length = w.length + 1 := by simp [step]
    cases hk : k w.length with
    | false =>
      have ⟨hd, he⟩ := hcut hk
      have hr : Maps (step w g) v (put r w.length (d w.length)) := by
        intro j hj
        rw [len] at hj
        by_cases e : j = w.length
        · subst j
          exact ⟨by simpa [put] using lt_of_lt_of_le hd hp.1, by
            simpa [put, step, read_last] using (hp.2 _ hd).trans he⟩
        · have hj' : j < w.length := by omega
          simpa only [put, ite_eq_right e, step, read_append _ hj'] using hm j hj'
      simpa only [compile, hk, Bool.false_eq_true, ite_false, List.foldl_cons, len] using
        ih (step w g) v (put r w.length (d w.length)) hp hr (len ▸ hback') hcut'
    | true =>
      let g' := renameGate r g
      have he : gateValue v g' = gateValue w g := by
        apply congrArg g.op.eval
        simp only [g', renameGate, List.map_map]
        exact List.map_congr_left fun j hj => (hm j (hback j hj)).2
      have len' : (step v g').length = v.length + 1 := by simp [step]
      have hp' : Prefix b (step v g') := by
        refine ⟨by rw [len']; exact Nat.le.step hp.1, ?_⟩
        intro j hj
        exact (read_append _ (lt_of_lt_of_le hj hp.1)).trans (hp.2 j hj)
      have hr : Maps (step w g) (step v g') (put r w.length v.length) := by
        intro j hj
        rw [len] at hj
        by_cases e : j = w.length
        · subst j
          exact ⟨by simp [put, len'], by simpa [put, step, read_last] using he⟩
        · have hj' : j < w.length := by omega
          obtain ⟨hjv, hjval⟩ := hm j hj'
          exact ⟨by simp [put, e, len']; omega, by
            simpa only [put, ite_eq_right e, step, read_append _ hj', read_append _ hjv] using hjval⟩
      simpa only [compile, hk, ite_true, List.foldl_cons, len, len', g'] using
        ih (step w g) (step v g') (put r w.length v.length) hp' hr (len ▸ hback') hcut'

private theorem length_fold (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step]; omega

private theorem read_fold {w : List Bool} (gs : List Gate) {j : Nat} (h : j < w.length) :
    (gs.foldl step w).getD j false = w.getD j false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    exact (ih (w := step w g) (by simp [step]; omega)).trans (read_append _ h)

/-- Check boundary ports directly against the full project trace, indexed by wire
number. This avoids any recursive proof about the values of cut gates. -/
theorem cutValues_of_wires (k : Nat → Bool) (d : Nat → Nat) (b w : List Bool) (gs : List Gate)
    (h : ∀ j, w.length ≤ j → j < w.length + gs.length → k j = false →
      d j < b.length ∧ b.getD (d j) false = (gs.foldl step w).getD j false) :
    CutValues k d b w gs := by
  induction gs generalizing w with
  | nil => trivial
  | cons g gs ih =>
    have len : (step w g).length = w.length + 1 := by simp [step]
    constructor
    · intro hk
      have ⟨hd, he⟩ := h w.length (by omega) (by simp) hk
      refine ⟨hd, he.trans ?_⟩
      change (gs.foldl step (step w g)).getD w.length false = _
      rw [read_fold gs (by rw [len]; omega)]
      exact read_last _ _
    · apply ih
      intro j ha hb
      apply h j <;> simp_all <;> omega

open PEqualNP.MetaComplexity.NestedCover

private theorem back_iff (gs : List Gate) (i : Nat) :
    Back i gs ↔ ∀ t g, gs[t]? = some g → ∀ j ∈ g.inputs, j < i + t := by
  induction gs generalizing i with
  | nil => simp [Back]
  | cons a gs ih =>
    constructor
    · rintro ⟨ha, hgs⟩ (_ | t) g he
      · obtain rfl : a = g := by simpa using he
        simpa using ha
      · have hh := (ih (i+1)).mp hgs t g (by simpa using he)
        simpa [Nat.add_assoc, Nat.add_comm 1 t] using hh
    · intro h
      refine ⟨by simpa using h 0 a (by simp), (ih (i+1)).mpr ?_⟩
      intro t g he
      simpa [Nat.add_assoc, Nat.add_comm 1 t] using h (t+1) g (by simpa using he)

theorem back_iff_readsBack (C : Circuit) (n : Nat) :
    Back n C.gates ↔ ReadsBack n C := by
  rw [back_iff]
  constructor
  · intro h j hj
    apply h j
    simp [gateAt, List.getElem?_eq_getElem hj]
  · intro h j g he
    have hj : j < C.gates.length := by
      by_contra! hn
      rw [List.getElem?_eq_none hn] at he
      contradiction
    simpa [gateAt, List.getD_eq_getElem?_getD, he] using h j hj

/-- If the primary wires and the omitted gates have their old Boolean values on
their selected ports, the extracted circuit computes exactly the old output. -/
theorem eval_extract (C : Circuit) (x b : List Bool) (k : Nat → Bool) (d : Nat → Nat)
    (hb : ReadsBack x.length C) (out : C.output < x.length + C.gates.length)
    (inputs : ∀ j < x.length, d j < b.length ∧ b.getD (d j) false = x.getD j false)
    (cuts : ∀ j, x.length ≤ j → j < x.length + C.gates.length → k j = false →
      d j < b.length ∧ b.getD (d j) false = (C.wires x).getD j false) :
    (extract C x.length b.length k d).eval b = C.eval x := by
  have hh := simulate k d b C.gates x b d ⟨le_rfl, fun _ _ => rfl⟩ inputs
    ((back_iff_readsBack ..).mpr hb) (cutValues_of_wires k d b x C.gates cuts)
  exact (hh C.output (by rw [length_fold]; exact out)).2

def Range (i m : Nat) (r : Nat → Nat) := ∀ j < i, r j < m
def BinaryAO (g : Gate) := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

theorem compile_shape (k : Nat → Bool) (d : Nat → Nat) (gs : List Gate)
    (i m : Nat) (r : Nat → Nat) (hr : Range i m r) (hb : Back i gs)
    (hg : ∀ g ∈ gs, BinaryAO g)
    (hd : ∀ j, i ≤ j → j < i + gs.length → k j = false → d j < m) :
    let p := compile k d i m r gs
    Back m p.1 ∧ (∀ g ∈ p.1, BinaryAO g) ∧ Range (i + gs.length) (m + p.1.length) p.2 := by
  induction gs generalizing i m r with
  | nil => simpa [compile, Back] using hr
  | cons g gs ih =>
    obtain ⟨hbefore, hrest⟩ := hb
    have hg' : ∀ a ∈ gs, BinaryAO a := fun a ha => hg a (List.mem_cons_of_mem _ ha)
    have hd' : ∀ j, i+1 ≤ j → j < i+1+gs.length → k j = false → d j < m := by
      intro j h₁ h₂
      exact hd j (by omega) (by simp; omega)
    cases hk : k i with
    | false =>
      have hri : Range (i+1) m (put r i (d i)) := by
        intro j hj
        by_cases hj' : j = i
        · subst j; simpa [put] using hd i (by omega) (by simp) hk
        · simpa [put, hj'] using hr j (by omega)
      simpa [compile, hk, Nat.add_assoc, Nat.add_comm 1 gs.length] using
        ih (i+1) m (put r i (d i)) hri hrest hg' hd'
    | true =>
      have hri : Range (i+1) (m+1) (put r i m) := by
        intro j hj
        by_cases hj' : j = i
        · simp [put, hj']
        · have h := hr j (by omega)
          simp [put, hj']; omega
      obtain ⟨hbr, hgr, hrr⟩ := ih (i+1) (m+1) (put r i m) hri hrest hg'
        (fun j h₁ h₂ h₃ => Nat.lt_succ_of_lt (hd' j h₁ h₂ h₃))
      simp only [compile, hk, ite_true, List.length_cons]
      refine ⟨⟨?_, hbr⟩, ?_, ?_⟩
      · intro j hj
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hj
        exact hr _ (hbefore _ ha)
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · simpa [BinaryAO, renameGate] using hg g (by simp)
        · exact hgr a ha
      · simpa [Nat.add_assoc, Nat.add_comm 1] using hrr

theorem isAO2_extract (C : Circuit) (n m : Nat) (k : Nat → Bool) (d : Nat → Nat)
    (hC : PEqualNP.TopForm.IsAO2 n C) (inputs : Range n m d)
    (cuts : ∀ j, n ≤ j → j < n+C.gates.length → k j = false → d j < m) :
    PEqualNP.TopForm.IsAO2 m (extract C n m k d) := by
  obtain ⟨hop, hb, hlen⟩ := hC
  have ⟨hback, hg, _⟩ := compile_shape k d C.gates n m d inputs ((back_iff_readsBack ..).mpr hb)
    (fun g h => ⟨hop g h, hlen g h⟩) cuts
  exact ⟨fun g h => (hg g h).1, (back_iff_readsBack ..).mp hback, fun g h => (hg g h).2⟩

/-- An input carries its own identifier. A gate carries the union of all its operands'
structural input supports, regardless of its Boolean operator. -/
def supportTrace (n : Nat) (C : Circuit) : List (Finset (Fin n)) :=
  PEqualNP.MetaComplexity.Helpers.suppsFrom C.gates (PEqualNP.MetaComplexity.Helpers.inputSupps n)

def mixed (n : Nat) (C : Circuit) (left right : Finset (Fin n)) (wire : Nat) : Bool :=
  let support := (supportTrace n C).getD wire ∅
  !Disjoint support left && !Disjoint support right

def core (n : Nat) (C : Circuit) (left right : Finset (Fin n)) : Circuit :=
  extract C n (n+C.gates.length) (mixed n C left right) id

/-- The canonical core gives a potential port to each original wire. Only primary
or omitted wires can be read through these ports, and all mixed gates are inner gates. -/
theorem core_spec (n : Nat) (C : Circuit) (left right : Finset (Fin n))
    (hC : PEqualNP.TopForm.IsAO2 n C) (out : C.output < n + C.gates.length) :
    (core n C left right).size = countFrom (mixed n C left right) n C.gates ∧
    PEqualNP.TopForm.IsAO2 (n+C.gates.length) (core n C left right) ∧
    ∀ x : List Bool, x.length = n →
      (core n C left right).eval (C.wires x) = C.eval x := by
  refine ⟨size_extract .., isAO2_extract _ _ _ _ _ hC (fun j h => by simp; omega)
    (fun j _ h _ => h), ?_⟩
  intro x hx
  have hlen : (C.wires x).length = n + C.gates.length := by
    change (C.gates.foldl step x).length = _
    rw [length_fold, hx]
  have he := eval_extract C x (C.wires x) (mixed n C left right) id
    (hx ▸ hC.2.1) (hx ▸ out) (fun j hj => ⟨by simp [hlen]; omega, read_fold C.gates hj⟩)
    (fun j _ h _ => ⟨by simpa [hlen, hx] using h, rfl⟩)
  simpa [core, hx, hlen] using he

#print axioms core_spec
end MixedExtract
