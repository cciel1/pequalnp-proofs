import Mathlib
import PEqualNP.Outside.L_meta_4063
import PEqualNP.Outside.L_meta_8137
import PEqualNP.Outside.L_meta_8608
import PEqualNP.Outside.R_meta_8031_401

/-!
# Completeness of the G11 packed circuit search

The verbatim project targets L-meta-8031 and L-meta-8610 are equivalent.
The reverse implication is the previously checked R-meta-8031-401 with L-meta-8608.
For the converse, nonconstant monotone fan-in-at-most-two circuits are normalized
to the same number of earlier-reading exactly-binary gates, preserving output
and all old dirty AND gate indices. The result also covers empty input lists,
repeated reads, forward references, and gates outside the output cone.
-/


namespace G11Normalize

/-- A column contains the value of one wire at every tested assignment. -/
abbrev Table (U : Type) := Nat → U → Bool
def Constant {U : Type} (v : U → Bool) : Prop := ∃ b, ∀ u, v u = b
def combine (isAnd a b : Bool) : Bool := if isAnd then a && b else a || b

/-- An absent operand supplies the neutral element. A forward read is a constant false
operand. Both of these are representable by the left constructor. -/
abbrev Arg (w : Nat) := Bool ⊕ Fin w
def argVal {U : Type} (V : Table U) {w : Nat} (a : Arg w) : U → Bool :=
  fun u => a.elim id (fun i => V i u)

noncomputable def normalized {U : Type} (n : Nat) (V : Table U) (w : Nat) (u : U) : Bool := by
  classical
  exact if n ≤ w ∧ Constant (V w) then V 0 u else V w u

private theorem resolve {U : Type} (n : Nat) (V : Table U) {w : Nat} (a : Arg w) :
    (∃ b, ∀ u, argVal V a u = b) ∨
    (∃ i : Fin w, ∀ u, argVal V a u = normalized n V i.val u) := by
  classical
  cases a with
  | inl b => exact Or.inl ⟨b,fun _ => rfl⟩
  | inr i =>
    by_cases h : Constant (V i)
    · exact Or.inl h
    · exact Or.inr ⟨i,fun u => by change V i u = normalized n V i u; simp [normalized,h]⟩

/-- One gate normalization keeps its gate slot and an old AND still has the AND tag.
Constant columns use a dummy AND at input zero. Nonconstants preserve their exact column. -/
theorem gate_normalization {U : Type} (n : Nat) (hn : 0<n) (V : Table U) {w : Nat}
    (hw : n ≤ w) (oldOp : Bool) (left right : Arg w)
    (rule : ∀ u, V w u = combine oldOp (argVal V left u) (argVal V right u)) :
    ∃ (op : Bool) (a b : Fin w), (oldOp = true → op = true) ∧
      ∀ u, normalized n V w u = combine op (normalized n V a u) (normalized n V b u) := by
  classical
  by_cases hwc : Constant (V w)
  · refine ⟨true,⟨0,by omega⟩,⟨0,by omega⟩,fun _ => rfl,?_⟩
    intro u
    simp [normalized,hw,hwc,show ¬ n ≤ 0 by omega,combine]
  have same (u : U) : normalized n V w u = V w u := by simp [normalized,hwc]
  have dup (op : Bool) (x : Bool) : combine op x x = x := by cases op <;> simp [combine]
  have copy (i : Fin w) (hi : ∀ u, V w u = normalized n V i.val u) :
      ∃ (op : Bool) (a b : Fin w), (oldOp = true → op = true) ∧
        ∀ u, normalized n V w u = combine op (normalized n V a u) (normalized n V b u) :=
    ⟨oldOp,i,i,id,fun u => by rw [same,hi,dup]⟩
  rcases resolve n V left with ⟨c, hc⟩ | ⟨a, ha⟩ <;>
    rcases resolve n V right with ⟨d, hd⟩ | ⟨b, hb⟩
  · exact (hwc ⟨combine oldOp c d,fun u => by rw [rule,hc,hd]⟩).elim
  · cases oldOp <;> cases c
    · exact copy b (fun u => by simp [rule u,hc u,hb u,combine])
    · exact (hwc ⟨true, fun u => by simp [rule u,hc u,combine]⟩).elim
    · exact (hwc ⟨false, fun u => by simp [rule u,hc u,combine]⟩).elim
    · exact copy b (fun u => by simp [rule u,hc u,hb u,combine])
  · cases oldOp <;> cases d
    · exact copy a (fun u => by simp [rule u,hd u,ha u,combine])
    · exact (hwc ⟨true, fun u => by simp [rule u,hd u,combine]⟩).elim
    · exact (hwc ⟨false, fun u => by simp [rule u,hd u,combine]⟩).elim
    · exact copy a (fun u => by simp [rule u,hd u,ha u,combine])
  · exact ⟨oldOp,a,b,id,fun u => by rw [same,rule,ha,hb]⟩

/-- Normalize all slots simultaneously. Every AND which was true on a distinguished row
is still an AND true on a distinguished row; only the witness row can change. -/
theorem normalize {U : Type} {n k : Nat} (hn : 0<n) (V : Table U)
    (oldOp : Fin k → Bool) (s t : (j : Fin k) → Arg (n+j.val))
    (rule : ∀ (j : Fin k) u, V (n+j.val) u =
      combine (oldOp j) (argVal V (s j) u) (argVal V (t j) u))
    (bad : U → Prop) (anchor : ∃ u, bad u ∧ V 0 u = true) :
    ∃ (op : Fin k → Bool) (a b : (j : Fin k) → Fin (n+j.val)),
      (∀ j u, normalized n V (n+j.val) u =
         combine (op j) (normalized n V (a j).val u) (normalized n V (b j).val u)) ∧
      ∀ j, oldOp j = true → (∃ u, bad u ∧ V (n+j.val) u = true) →
        op j = true ∧ ∃ u, bad u ∧ normalized n V (n+j.val) u = true := by
  classical
  choose op a b hop hval using fun j => gate_normalization n hn V (Nat.le_add_right n j.val)
    (oldOp j) (s j) (t j) (rule j)
  refine ⟨op,a,b,hval,?_⟩
  intro j hj dirty
  refine ⟨hop j hj,?_⟩
  by_cases c : Constant (V (n+j.val))
  · obtain ⟨u,hneg,hu⟩ := anchor
    exact ⟨u,hneg,by simpa [normalized,c] using hu⟩
  · obtain ⟨u,hneg,hu⟩ := dirty
    exact ⟨u,hneg,by simpa [normalized,c] using hu⟩

#print axioms normalize
end G11Normalize

namespace G11Normalize
open PEqualNP CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover EdgeOwnership CleanedNonEdge TopForm
open Outside.L_meta_8137

abbrev val {n : Nat} (C : Circuit) : Table (Fin n → Bool) :=
  fun w x => BlindGate.wireValue C n x w

@[simp] private theorem argVal_const {U : Type} (V : Table U) {w : Nat} (b : Bool) (u : U) :
    argVal V (Sum.inl b : Arg w) u = b := rfl

private def boundArg (w i : Nat) : Arg w := if h : i < w then .inr ⟨i,h⟩ else .inl false

private theorem bound_val {U : Type} (V : Table U) (w i : Nat) (u : U) :
    argVal V (boundArg w i) u = if i < w then V i u else false := by
  by_cases h : i<w <;> simp only [boundArg,h, dite_true,dite_false,ite_true,ite_false] <;> rfl

private theorem raw_gate {n : Nat} {C : Circuit} (hm : Monotone2 C) (j : Fin C.size) :
    ∃ (op : Bool) (s t : Arg (n+j.val)), ((gateAt C j.val).op = .and → op = true) ∧
     ∀ x, val (n:=n) C (n+j.val) x = combine op (argVal (val C) s x) (argVal (val C) t x) := by
  let g := C.gates[j.val]'j.isLt
  obtain ⟨opOK, fanin⟩ := hm g (List.getElem_mem j.isLt)
  have gspec : gateAt C j.val = g := gateAt_eq j.isLt
  have raw (x : Fin n → Bool) : val C (n+j.val) x =
      g.op.eval (g.inputs.map (fun i => argVal (val C) (boundArg (n+j.val) i) x)) := by
    have e := W_gate C.gates (List.ofFn x) j.val (by exact j.isLt)
    rw [List.length_ofFn] at e
    unfold val BlindGate.wireValue
    simpa only [bound_val, wires_W] using e
  have finish : ∀ (op : Bool) (s t : Arg (n+j.val)), (g.op = .and → op = true) →
      (∀ x : Fin n → Bool, g.op.eval (g.inputs.map (fun i => argVal (val C) (boundArg (n+j.val) i) x)) =
        combine op (argVal (val C) s x) (argVal (val C) t x)) →
      ∃ (b : Bool) (l r : Arg (n+j.val)), ((gateAt C j.val).op = .and → b = true) ∧
        ∀ x : Fin n → Bool, val C (n+j.val) x = combine b (argVal (val C) l x) (argVal (val C) r x) := by
    intro op s t tag eqn
    exact ⟨op,s,t,by rw [gspec];exact tag,fun x => (raw x).trans (eqn x)⟩
  rcases opOK with hand | hor
  · cases he : g.inputs with
    | nil => exact finish true (.inl true) (.inl true) (fun _ => rfl) (by simp [he,hand,combine,GateOp.eval])
    | cons a tail =>
      cases tail with
      | nil => exact finish true (boundArg _ a) (.inl true) (fun _ => rfl) (by simp [he,hand,combine,GateOp.eval])
      | cons b tail =>
        cases tail with
        | nil => exact finish true (boundArg _ a) (boundArg _ b) (fun _ => rfl) (by simp [he,hand,combine,GateOp.eval])
        | cons c cs => simp [he] at fanin
  · change g.op = .or at hor
    have tag : g.op = .and → false = true := by simp [hor]
    cases he : g.inputs with
    | nil => exact finish false (.inl false) (.inl false) tag (by simp [he,hor,combine,GateOp.eval])
    | cons a tail =>
      cases tail with
      | nil => exact finish false (boundArg _ a) (.inl false) tag (by simp [he,hor,combine,GateOp.eval])
      | cons b tail =>
        cases tail with
        | nil => exact finish false (boundArg _ a) (boundArg _ b) tag (by simp [he,hor,combine,GateOp.eval])
        | cons c cs => simp [he] at fanin

def mkCircuit {n k : Nat} (op : Fin k → Bool) (a b : (j : Fin k) → Fin (n+j.val)) (w : Nat) : Circuit :=
  { gates := List.ofFn (fun j => ⟨if op j then .and else .or,[(a j).val,(b j).val]⟩), output := w }

private theorem model_shape {n k : Nat} (op : Fin k → Bool) (a b : (j : Fin k) → Fin (n+j.val)) (w : Nat) :
    IsAO2 n (mkCircuit op a b w) := by
  let gate : Fin k → Gate := fun j => ⟨if op j then .and else .or,[(a j).val,(b j).val]⟩
  change AndOrOnly ⟨List.ofFn gate,w⟩ ∧ ReadsBack n ⟨List.ofFn gate,w⟩ ∧ _
  refine ⟨?_,?_,?_⟩
  · intro g hg
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hg
    simp only [gate]
    cases op j <;> simp
  · intro i hi q hq
    have hi' : i < k := by simpa using hi
    let j : Fin k := ⟨i,hi'⟩
    have eqg : gateAt ⟨List.ofFn gate,w⟩ i = gate j := by
      rw [gateAt_eq hi]; simp [j]
    rw [eqg] at hq
    obtain hx|hx : q=(a j).val ∨ q=(b j).val := by simpa [gate] using hq
    · exact hx ▸ (a j).isLt
    · exact hx ▸ (b j).isLt
  · intro g hg
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hg
    rfl

private theorem model_value {U : Type} {n k : Nat} (row : U → Fin n → Bool)
    (V : Table U) (op : Fin k → Bool) (a b : (j : Fin k) → Fin (n+j.val)) (w : Nat)
    (inputs : ∀ (i : Fin n) u, V i u = row u i)
    (gates : ∀ (j : Fin k) u, V (n+j.val) u = combine (op j) (V (a j) u) (V (b j) u)) :
    ∀ s < n+k, ∀ u, val (mkCircuit op a b w) s (row u) = V s u := by
  let D := mkCircuit op a b w
  have rb := (model_shape op a b w).2.1
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro hs u
    by_cases hp : s < n
    · exact (wv_input D (row u) s hp).trans (inputs ⟨s,hp⟩ u).symm
    obtain ⟨j,e⟩ : ∃ j : Fin k, s = n+j.val := ⟨⟨s-n,by omega⟩,by simp;omega⟩
    subst s
    have hj : j.val < D.gates.length := by simp [D,mkCircuit]
    change BlindGate.wireValue D n (row u) (n+j.val) = _
    rw [wv_gate D rb _ j.val hj, gates j u]
    have eqg : (D.gates[j.val]'hj) = ⟨if op j then .and else .or,[(a j).val,(b j).val]⟩ := by simp [D,mkCircuit]
    rw [eqg]
    have ha := ih (a j).val (a j).isLt (by have := (a j).isLt; omega) u
    have hb := ih (b j).val (b j).isLt (by have := (b j).isLt; omega) u
    change BlindGate.wireValue D n (row u) (a j).val = _ at ha
    change BlindGate.wireValue D n (row u) (b j).val = _ at hb
    cases hop : op j <;> simp [GateOp.eval,combine,ha,hb]

/-- Preserve size, output and every dirty AND gate index while eliminating all non-earlier
reads and all nonbinary gates. All finite assignments are represented, not only test rows. -/
theorem normalize_circuit {n : Nat} (hn : 0<n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hm : Monotone2 C)
    (nonconst : ¬ Constant (fun x : Fin n → Bool => C.eval (List.ofFn x))) :
    ∃ D : Circuit, D.size = C.size ∧ D.output = C.output ∧ IsAO2 n D ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧ junk G C ⊆ junk G D := by
  classical
  choose old s t andtag hraw using fun j => raw_gate (n:=n) hm j
  let V := val (n:=n) C
  have hanchor : ∃ x, graphFun G ∅ x = false ∧ V 0 x = true := by
    let z : Fin n := ⟨0,hn⟩
    let x : Fin n → Bool := fun p => decide (p = z)
    refine ⟨x,?_,(wv_input C x 0 hn).trans (by simp [x,z])⟩
    simp [graphFun,x]
  obtain ⟨op,a,b,hval,hmark⟩ := normalize hn V old s t hraw (fun x => graphFun G ∅ x = false) hanchor
  let D := mkCircuit op a b C.output
  have sz : D.size = C.size := by simp [D,mkCircuit,Circuit.size]
  have iread (i : Fin n) (x : Fin n → Bool) : normalized n V i.val x = x i := by
    simpa [normalized,not_le.mpr i.isLt,V] using (wv_input C x i.val i.isLt)
  have truth := model_value id (normalized n V) op a b C.output iread hval
  have hwo : C.output < n+C.size := by
    by_contra! ho
    exact nonconst ⟨false,fun x => wv_ge C x C.output ho⟩
  refine ⟨D,sz,rfl,model_shape op a b _,?_,?_⟩
  · intro x
    have e := truth C.output hwo x
    change D.eval (List.ofFn x) = normalized n V C.output x at e
    change D.eval (List.ofFn x) = V C.output x
    simpa [normalized,show ¬ Constant (V C.output) from nonconst] using e
  · intro j hj
    obtain ⟨hj,hand,_,x,hx,he⟩ := Finset.mem_filter.mp hj
    have hj' : j < C.size := Finset.mem_range.mp hj
    let i : Fin C.size := ⟨j,hj'⟩
    obtain ⟨tag,u,hu,hgate⟩ := hmark i (andtag i hand) ⟨x,he,hx⟩
    have hD : j < D.gates.length := by change j < D.size; omega
    have eqg : (gateAt D j).op = .and := by
      rw [gateAt_eq hD]
      simpa [D,mkCircuit,i] using (show (if op i then GateOp.and else GateOp.or) = .and by simp [tag])
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hD,eqg,hD,u,?_,hu⟩
    exact (truth (n+j) (by omega) u).trans hgate

#print axioms normalize_circuit
end G11Normalize

namespace G11Search
open PEqualNP CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover
open EdgeOwnership CleanedNonEdge TopForm

abbrev edgeList : List (ℕ × ℕ) :=
  [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
   (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
abbrev graph := edgeGraph 11 edgeList
abbrev negatives : List ℕ :=
  [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]
abbrev row (i : Fin 24) : Fin 11 → Bool := fun p => negatives[i.val].testBit p.val

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem independent_rows : ∀ i : Fin 24, graphFun graph ∅ (row i) = false := by decide +kernel

/-- Complete 24-row test for junk at an arbitrary AND/OR gate, including garbage gates,
with arbitrary fan-in and arbitrary natural-number wire references. -/
theorem junk_iff {C : Circuit} (h : AndOrOnly C) (j : Nat) :
    j ∈ junk graph C ↔ j < C.size ∧ (gateAt C j).op = .and ∧
      ∃ r : Fin 24, gateVal 11 C j (row r) = true := by
  constructor
  · intro hj
    obtain ⟨_,hand,hj,x,hx,he⟩ := Finset.mem_filter.mp hj
    refine ⟨hj,hand,?_⟩
    by_contra! none
    have zero (m : Nat) (hm : m ∈ negatives) :
        gateVal 11 C j (fun p : Fin 11 => m.testBit p.val) = false := by
      obtain ⟨k,hk,e⟩ := List.mem_iff_getElem.mp hm
      subst m
      exact Bool.eq_false_iff.mpr (none ⟨k,hk⟩)
    have sub := Outside.L_meta_4063 C j h zero
    exact Bool.noConfusion ((sub x hx).symm.trans he)
  · rintro ⟨hj,hand,r,hit⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hand,hj,row r,hit,independent_rows r⟩

open Classical in
/-- Exact count on the 24 maximal negatives, for arbitrary circuit syntax. -/
theorem junk_eq_filter {C : Circuit} (h : AndOrOnly C) :
    junk graph C = (Finset.range C.size).filter (fun j =>
      (gateAt C j).op = .and ∧ ∃ r : Fin 24, gateVal 11 C j (row r) = true) := by
  ext j
  simp [junk_iff h]

#print axioms junk_iff
#print axioms junk_eq_filter
end G11Search

namespace G11Search
open PEqualNP CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover EdgeOwnership TopForm
open G11Normalize

/-- Official public assignment statement, verbatim from the desk manifest. -/
def Official8031 : Prop :=
  have x1 : List (Fin (11 : ℕ) × Fin (11 : ℕ)) := [((0 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))), ((0 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))), ((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((1 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))), ((3 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))), ((3 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))), ((4 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))), ((4 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))), ((5 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))), ((5 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))), ((7 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))), ((8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)))]; have x2 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)]; ∃ (x3 : Fin (22 : ℕ)) (x4 : Fin ↑x3 → Bool) (x5 : Fin ↑x3 → Option (Fin (33 : ℕ)) × Option (Fin (33 : ℕ))) (x6 : Fin (33 : ℕ)),   have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.ofFn fun (x7 : Fin ↑x3) => { op := if x4 x7 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or, inputs := List.map Fin.val ((x5 x7).1.toList ++ (x5 x7).2.toList) : PEqualNP.CircuitLowerBounds.Gate }, output := ↑x6 : PEqualNP.CircuitLowerBounds.Circuit };   (∀ x8 ∈ x1, x7.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput x8.1 x8.2)) = Bool.true) ∧ (∀ x8 ∈ x2, x7.eval (List.ofFn fun (x10 : Fin (11 : ℕ)) => x8.testBit ↑x10) = Bool.false) ∧ (3 : ℕ) ≤ (PEqualNP.TopForm.junk (PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x8 : Fin (11 : ℕ) × Fin (11 : ℕ)) => (↑x8.1, ↑x8.2)) x1)) x7).card

abbrev edges : List (Fin 11 × Fin 11) :=
  [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
   (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

def Positive (C : Circuit) : Prop :=
  ∀ e ∈ edges, C.eval (List.ofFn (pairInput e.1 e.2)) = true
def Negative (C : Circuit) : Prop :=
  ∀ m ∈ negatives, C.eval (List.ofFn (fun i : Fin 11 => m.testBit i.val)) = false

private def raw {k : Fin 22} (op : Fin k.val → Bool)
    (args : Fin k.val → Option (Fin 33) × Option (Fin 33)) (out : Fin 33) : Circuit :=
  {gates := List.ofFn fun j => ⟨if op j then .and else .or,
      ((args j).1.toList ++ (args j).2.toList).map Fin.val⟩, output := out.val}

private theorem raw_monotone {k : Fin 22} (op args out) : Monotone2 (raw (k:=k) op args out) := by
  intro g hg
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hg
  constructor
  · cases e : op j <;> simp
  · cases (args j).1 <;> cases (args j).2 <;> simp

private theorem nonconstant {C : Circuit} (pos : Positive C) (neg : Negative C) :
    ¬ Constant (fun x : Fin 11 → Bool => C.eval (List.ofFn x)) := by
  rintro ⟨b,h⟩
  have p := pos (0,9) (by decide)
  have m := neg 15 (by decide)
  have hp := (h (pairInput (n:=11) 0 9)).symm.trans p
  have hq := (h (fun i : Fin 11 => (15 : Nat).testBit i.val)).symm.trans m
  exact Bool.noConfusion (hp.symm.trans hq)

theorem earlier_pair {C : Circuit} (ao : IsAO2 11 C) (small : C.size ≤ 21)
    (j : Fin C.size) : ∃ a b : Fin 33, C.gates[j.val].inputs = [a.val,b.val] := by
  let g := C.gates[j.val]
  change ∃ a b : Fin 33, g.inputs = [a.val,b.val]
  have hgm : g ∈ C.gates := List.getElem_mem j.isLt
  have len := ao.2.2 g hgm
  have lookup : gateAt C j.val = g := Outside.L_meta_8137.gateAt_eq (C:=C) j.isLt
  rcases he : g.inputs with _ | ⟨a,_ | ⟨b,_ | ⟨c,t⟩⟩⟩
  · simp [he] at len
  · simp [he] at len
  · have ea := ao.2.1 j.val j.isLt a (by rw [lookup,he]; simp)
    have eb := ao.2.1 j.val j.isLt b (by rw [lookup,he]; simp)
    exact ⟨⟨a,by omega⟩,⟨b,by omega⟩,rfl⟩
  · simp [he] at len

private theorem circ_ext {C D : Circuit} (a : C.gates = D.gates) (b : C.output = D.output) : C = D := by
  cases C; cases D; simp_all

/-- Equivalence with the earlier-wire exactly-binary search across all 21 gates.
Input repetition and unused gates are allowed. -/
theorem exact_search_iff : Official8031 ↔ ∃ C : Circuit, C.size ≤ 21 ∧ IsAO2 11 C ∧
    Positive C ∧ Negative C ∧ 3 ≤ (junk graph C).card := by
  classical
  constructor
  · rintro ⟨k,op,args,out,pos,neg,junkNum⟩
    let C := raw op args out
    change Positive C at pos
    change Negative C at neg
    change 3 ≤ (junk graph C).card at junkNum
    have bound : C.size ≤ 21 := by
      have hk := k.isLt
      simp [C,raw,Circuit.size]; omega
    obtain ⟨D,sz,_,ao,identical,subset⟩ := normalize_circuit (by decide : 0<11) graph C
      (raw_monotone op args out) (nonconstant pos neg)
    exact ⟨D,sz ▸ bound,ao,fun e he => (identical _).trans (pos e he),
      fun m hm => (identical _).trans (neg m hm),junkNum.trans (Finset.card_le_card subset)⟩
  · rintro ⟨C,small,ao,pos,neg,junkNum⟩
    let k : Fin 22 := ⟨C.size,by omega⟩
    choose a b hab using earlier_pair ao small
    let op (j : Fin C.size) : Bool := decide (C.gates[j.val].op = .and)
    let args (j : Fin C.size) : Option (Fin 33) × Option (Fin 33) := (some (a j),some (b j))
    have out_ok : C.output < 11 + C.size := by
      by_contra! bad
      have hm := pos (0,9) (by decide)
      have zero := Outside.L_meta_8137.wv_ge C (pairInput (n:=11) 0 9) C.output bad
      change C.eval (List.ofFn (pairInput (n:=11) 0 9)) = false at zero
      exact Bool.noConfusion (hm.symm.trans zero)
    let out : Fin 33 := ⟨C.output,by omega⟩
    have eq : raw (k:=k) op args out = C := by
      apply circ_ext
      · apply List.ext_getElem
        · simp [raw,k,Circuit.size]
        · intro i hi hi'
          let j : Fin C.size := ⟨i,hi'⟩
          let build (j : Fin C.size) : Gate :=
            ⟨if op j then .and else .or,[(a j).val,(b j).val]⟩
          have hi2 : i < (List.ofFn build).length := by rw [List.length_ofFn];exact hi'
          change (List.ofFn build)[i]'hi2 = C.gates[i]
          refine (List.getElem_ofFn hi2).trans ?_
          let g := C.gates[i]
          have hg : g ∈ C.gates := List.getElem_mem hi'
          have pairs : g.inputs = [(a j).val,(b j).val] := hab j
          have ops := ao.1 g hg
          change ({op := if op j then .and else .or, inputs := [((a j).val),((b j).val)]} : Gate) = g
          cases hg' : g with | mk o ins =>
            rw [hg'] at pairs ops
            simp only at pairs ops
            subst ins
            have tag : op j = decide (o = .and) := by
              change decide (g.op = .and) = _; rw [hg']
            rcases ops with rfl | rfl <;> simp [tag]
      · rfl
    refine ⟨k,op,args,out,?_⟩
    change Positive (raw (k:=k) op args out) ∧ Negative (raw (k:=k) op args out) ∧
      3 ≤ (junk graph (raw (k:=k) op args out)).card
    exact eq ▸ ⟨pos,neg,junkNum⟩

#print axioms exact_search_iff
end G11Search

namespace G11Search
open PEqualNP CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover EdgeOwnership TopForm
open G11Normalize

/-- Verbatim public search subproblem L-meta-8610. -/
def Official8610 : Prop :=
  ∃ (x1 : Fin (22 : ℕ)) (x2 : Fin ↑x1 → Bool) (x3 : Fin ↑x1 → Fin (33 : ℕ)) (x4 : Fin ↑x1 → Fin (33 : ℕ)) (x5 : Fin (33 : ℕ)) (x6 : ℕ → ℕ) (x7 : Fin (3 : ℕ) → Fin ↑x1) (x8 : Fin (3 : ℕ) → Fin (24 : ℕ)), ↑x5 < (11 : ℕ) + ↑x1 ∧ x6 ↑x5 = (65535 : ℕ) ∧ (∀ (x9 : Fin (11 : ℕ)), x6 ↑x9 = [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].getD ↑x9 (0 : ℕ)) ∧ (∀ (x9 : Fin ↑x1), ↑(x3 x9) < (11 : ℕ) + ↑x9 ∧ ↑(x4 x9) < (11 : ℕ) + ↑x9 ∧ x6 ((11 : ℕ) + ↑x9) = if x2 x9 = Bool.true then x6 ↑(x3 x9) &&& x6 ↑(x4 x9) else x6 ↑(x3 x9) ||| x6 ↑(x4 x9)) ∧ Function.Injective x7 ∧ ∀ (x9 : Fin (3 : ℕ)), x2 (x7 x9) = Bool.true ∧ (x6 ((11 : ℕ) + ↑(x7 x9))).testBit ((16 : ℕ) + ↑(x8 x9)) = Bool.true

abbrev columns : List Nat := [2147418115,663661903884,34144976944,728266375360,21653750532,
    103293914128,26322415680,344922804352,414195942664,581968119809,1065151898146]

abbrev masks : List Nat := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768] ++ negatives

abbrev trial (u : Fin 40) (p : Fin 11) : Bool := masks[u.val]!.testBit p.val

def pack (f : Fin 40 → Bool) : Nat := (BitVec.ofBoolListLE (List.ofFn f)).toNat

private theorem pack_bit (f : Fin 40 → Bool) (i : Nat) :
    (pack f).testBit i = if h : i<40 then f ⟨i,h⟩ else false := by
  change (BitVec.ofBoolListLE _).getLsbD i = _
  rw [BitVec.getLsbD_ofBoolListLE]
  by_cases h : i<40
  · simp only [h,dite_true]
    exact Outside.L_meta_8137.ofFn_getD f i h
  · simp only [h,dite_false]
    exact Outside.L_meta_8137.getD_ge _ _ (by rw [List.length_ofFn]; omega)

private theorem pack_gate (a b : Fin 40 → Bool) (op : Bool) :
    pack (fun u => combine op (a u) (b u)) =
      if op then pack a &&& pack b else pack a ||| pack b := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases op <;> by_cases h : i<40 <;> simp [Nat.testBit_and,Nat.testBit_or,pack_bit,h,combine]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem inputs_table : ∀ i : Fin 11, pack (fun u => trial u i) = columns.getD i.val 0 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem mask_table : pack (fun u => decide (u.val < 16)) = 65535 := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
private theorem positive_table : ∀ u : Fin 40, u.val < 16 →
    ∃ e : Fin 11 × Fin 11, e ∈ edges ∧ trial u = pairInput e.1 e.2 := by decide +kernel

set_option maxRecDepth 8192 in
private theorem negative_table : ∀ r : Fin 24, trial ⟨16+r.val,by omega⟩ = row r := by decide +kernel

private theorem labels {C : Circuit} (pos : Positive C) (neg : Negative C) (u : Fin 40) :
    C.eval (List.ofFn (trial u)) = decide (u.val < 16) := by
  by_cases h : u.val < 16
  · obtain ⟨e,he,eq⟩ := positive_table u h
    rw [eq]
    simpa [h] using pos e he
  · let r : Fin 24 := ⟨u.val-16,by omega⟩
    have e : u = ⟨16+r.val,by omega⟩ := Fin.ext (by dsimp [r];omega)
    have hrow : trial u = row r := e ▸ negative_table r
    rw [hrow]
    simpa [h,row] using neg negatives[r.val] (List.getElem_mem (by exact r.isLt))

/-- The previously published packed synthesis target is necessary for every witness in the
unrestricted official language. The converse uses both published reduction premises. -/
theorem complete_packed_search : Official8031 ↔ Official8610 := by
  constructor
  · intro original
    classical
    obtain ⟨C,small,ao,pos,neg,junkNum⟩ := exact_search_iff.mp original
    let k : Fin 22 := ⟨C.size,by omega⟩
    choose a b pair using earlier_pair ao small
    let op (j : Fin C.size) := decide ((gateAt C j.val).op = GateOp.and)
    let W (w : Nat) (u : Fin 40) := val C w (trial u)
    let S (w : Nat) := pack (W w)
    have hout : C.output < 11+C.size := by
      by_contra! beyond
      have hit := pos (0,9) (by decide)
      have zero := Outside.L_meta_8137.wv_ge C (pairInput (n:=11) 0 9) C.output beyond
      exact Bool.noConfusion (hit.symm.trans zero)
    let out : Fin 33 := ⟨C.output,by omega⟩
    let J := junk graph C
    let select (i : Fin 3) : ↥J := J.orderIsoOfFin rfl ⟨i.val,by change 3≤J.card at junkNum;omega⟩
    let d (i : Fin 3) : Fin C.size := ⟨(select i).val, ((junk_iff ao.1 _).mp (select i).property).1⟩
    have data (i : Fin 3) := ((junk_iff ao.1 _).mp (select i).property).2
    choose q hit using fun i => (data i).2
    refine ⟨k,op,a,b,out,S,d,q,hout,?_,?_,?_,?_,?_⟩
    · change pack (W C.output) = 65535
      rw [← mask_table]
      exact congrArg pack (funext (labels pos neg))
    · intro i
      change pack (W i.val) = _
      rw [← inputs_table i]
      exact congrArg pack (funext (fun u => Outside.L_meta_8137.wv_input C (trial u) i.val i.isLt))
    · intro j
      have hp := pair j
      let g : Gate := C.gates[j.val]'j.isLt
      change g.inputs = [(a j).val,(b j).val] at hp
      have look : gateAt C j.val = g := Outside.L_meta_8137.gateAt_eq j.isLt
      have ea := ao.2.1 j.val j.isLt (a j).val (by rw [look,hp];simp)
      have eb := ao.2.1 j.val j.isLt (b j).val (by rw [look,hp];simp)
      refine ⟨ea,eb,?_⟩
      change pack (W (11+j.val)) = _
      rw [← pack_gate (W (a j).val) (W (b j).val) (op j)]
      apply congrArg pack
      funext u
      have eqn := Outside.L_meta_8137.wv_gate C ao.2.1 (trial u) j.val j.isLt
      change W (11+j.val) u = g.op.eval (g.inputs.map fun w => W w u) at eqn
      rw [eqn,hp]
      rcases ao.1 g (List.getElem_mem j.isLt) with h | h
      · simp [op,look,h,GateOp.eval,combine]
      · simp [op,look,h,GateOp.eval,combine]
    · intro i j e
      have same : select i = select j := Subtype.ext (congrArg Fin.val e)
      have h := (J.orderIsoOfFin rfl).injective same
      exact Fin.ext (congrArg (fun z : Fin J.card => z.val) h)
    · intro i
      refine ⟨by change decide ((gateAt C (select i).val).op = GateOp.and) = true
                 exact decide_eq_true (data i).1,?_⟩
      change (pack (W (11+(d i).val))).testBit (16+(q i).val) = true
      simp only [pack_bit,show 16+(q i).val<40 by have := (q i).isLt; omega,dite_true]
      change BlindGate.wireValue C 11 (trial _) (11+(d i).val) = true
      rw [negative_table]
      exact hit i
  · exact Outside.R_meta_8031_401 Outside.L_meta_8608

#print axioms complete_packed_search
end G11Search

namespace G11Search

/-- Number of walks of each length from 0 through 4 starting at each vertex. -/
def walkCount (k : Fin 5) (p : Fin 11) : Nat :=
  ([[1,1,1,1,1,1,1,1,1,1,1],
    [2,2,2,2,3,3,3,3,4,4,4],
    [8,7,7,6,10,10,9,9,12,12,10],
    [22,22,20,18,29,31,25,27,39,39,34],
    [73,68,65,52,95,98,79,82,121,119,96]] : List (List Nat))[k.val]!.getD p.val 0

private theorem base : ∀ p, walkCount 0 p = 1 := by decide
private theorem recurrence : ∀ (k : Fin 4) p, walkCount k.succ p =
    ∑ q : Fin 11, if graph.Adj p q then walkCount k.castSucc q else 0 := by decide +kernel
private theorem fourth : ∀ p q : Fin 11, walkCount 4 p = walkCount 4 q → p = q := by decide

/-- Every relabeling of the eleven primary inputs preserving graph adjacency is identity. -/
theorem no_vertex_symmetry (e : Equiv.Perm (Fin 11))
    (ha : ∀ p q, graph.Adj (e p) (e q) ↔ graph.Adj p q) : e = Equiv.refl _ := by
  have fixed (k : Fin 5) : ∀ p, walkCount k (e p) = walkCount k p := by
    induction k using Fin.induction with
    | zero => intro p; rw [base,base]
    | succ k ih =>
      intro p
      rw [recurrence,recurrence]
      calc
        _ = ∑ q : Fin 11, if graph.Adj (e p) (e q) then walkCount k.castSucc (e q) else 0 :=
          (Equiv.sum_comp e (fun q => if graph.Adj (e p) q then walkCount k.castSucc q else 0)).symm
        _ = _ := Finset.sum_congr rfl fun q _ => by simp only [ha,ih]
  exact Equiv.ext fun p => fourth _ _ (fixed 4 p)

#print axioms no_vertex_symmetry
end G11Search
