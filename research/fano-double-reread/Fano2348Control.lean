import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Fano2348Control

def gs : List Gate :=
  [⟨GateOp.or, [12, 7]⟩,
   ⟨GateOp.or, [13, 8]⟩,
   ⟨GateOp.or, [12, 11]⟩,
   ⟨GateOp.or, [9, 16]⟩,
   ⟨GateOp.or, [11, 8]⟩,
   ⟨GateOp.or, [9, 10]⟩,
   ⟨GateOp.or, [15, 9]⟩,
   ⟨GateOp.or, [10, 18]⟩,
   ⟨GateOp.and, [5, 17]⟩,
   ⟨GateOp.or, [14, 8]⟩,
   ⟨GateOp.or, [12, 10]⟩,
   ⟨GateOp.or, [7, 13]⟩,
   ⟨GateOp.and, [4, 21]⟩,
   ⟨GateOp.or, [11, 25]⟩,
   ⟨GateOp.and, [0, 27]⟩,
   ⟨GateOp.or, [7, 19]⟩,
   ⟨GateOp.or, [24, 13]⟩,
   ⟨GateOp.or, [28, 20]⟩,
   ⟨GateOp.or, [28, 2]⟩,
   ⟨GateOp.and, [3, 29]⟩,
   ⟨GateOp.and, [32, 31]⟩,
   ⟨GateOp.and, [6, 30]⟩,
   ⟨GateOp.and, [1, 23]⟩,
   ⟨GateOp.or, [36, 22]⟩,
   ⟨GateOp.or, [33, 26]⟩,
   ⟨GateOp.or, [35, 38]⟩,
   ⟨GateOp.or, [37, 39]⟩,
   ⟨GateOp.or, [40, 34]⟩]

def cc : Circuit := ⟨gs, 41⟩

def form (x : Fin 14 → Bool) : Bool :=
  ((((x 1 && (((x 12 || (x 7 || false)) || (x 8 || false)) && true)) || ((x 5 && ((x 9 || ((x 12 || (x 11 || false)) || false)) && true)) || false)) || (((x 6 && (((x 12 || (x 10 || false)) || (x 13 || false)) && true)) || (((x 3 && ((x 7 || ((x 9 || (x 10 || false)) || false)) && true)) || ((x 4 && ((x 10 || ((x 11 || (x 8 || false)) || false)) && true)) || false)) || false)) || false)) || ((((x 0 && ((x 11 || ((x 7 || (x 13 || false)) || false)) && true)) || (x 2 || false)) && (((x 0 && ((x 11 || ((x 7 || (x 13 || false)) || false)) && true)) || (((x 13 || (x 8 || false)) || (x 9 || false)) || false)) && true)) || false))

set_option maxRecDepth 12000 in
def run (g : List Gate) (w : List Bool) : List Bool := g.foldl (fun w q => w ++ [q.op.eval (q.inputs.map fun i => w.getD i false)]) w

theorem advance (q : Gate) (rest : List Gate) (w u : List Bool) (h : w ++ [q.op.eval (q.inputs.map fun i => w.getD i false)] = u) : run (q :: rest) w = run rest u := by
  subst u
  rfl

set_option maxHeartbeats 1500000 in
def expected (x : Fin 14 → Bool) : List Bool :=
  let b14 : Bool := (x 12 || (x 7 || false))
  let b15 : Bool := (x 13 || (x 8 || false))
  let b16 : Bool := (x 12 || (x 11 || false))
  let b17 : Bool := (x 9 || (b16 || false))
  let b18 : Bool := (x 11 || (x 8 || false))
  let b19 : Bool := (x 9 || (x 10 || false))
  let b20 : Bool := (b15 || (x 9 || false))
  let b21 : Bool := (x 10 || (b18 || false))
  let b22 : Bool := (x 5 && (b17 && true))
  let b23 : Bool := (b14 || (x 8 || false))
  let b24 : Bool := (x 12 || (x 10 || false))
  let b25 : Bool := (x 7 || (x 13 || false))
  let b26 : Bool := (x 4 && (b21 && true))
  let b27 : Bool := (x 11 || (b25 || false))
  let b28 : Bool := (x 0 && (b27 && true))
  let b29 : Bool := (x 7 || (b19 || false))
  let b30 : Bool := (b24 || (x 13 || false))
  let b31 : Bool := (b28 || (b20 || false))
  let b32 : Bool := (b28 || (x 2 || false))
  let b33 : Bool := (x 3 && (b29 && true))
  let b34 : Bool := (b32 && (b31 && true))
  let b35 : Bool := (x 6 && (b30 && true))
  let b36 : Bool := (x 1 && (b23 && true))
  let b37 : Bool := (b36 || (b22 || false))
  let b38 : Bool := (b33 || (b26 || false))
  let b39 : Bool := (b35 || (b38 || false))
  let b40 : Bool := (b37 || (b39 || false))
  let b41 : Bool := (b40 || (b34 || false))
  [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41]

theorem wireForm (x : Fin 14 → Bool) : cc.wires (List.ofFn x) = expected x := by
  have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13] := rfl
  let b14 : Bool := (x 12 || (x 7 || false))
  let b15 : Bool := (x 13 || (x 8 || false))
  let b16 : Bool := (x 12 || (x 11 || false))
  let b17 : Bool := (x 9 || (b16 || false))
  let b18 : Bool := (x 11 || (x 8 || false))
  let b19 : Bool := (x 9 || (x 10 || false))
  let b20 : Bool := (b15 || (x 9 || false))
  let b21 : Bool := (x 10 || (b18 || false))
  let b22 : Bool := (x 5 && (b17 && true))
  let b23 : Bool := (b14 || (x 8 || false))
  let b24 : Bool := (x 12 || (x 10 || false))
  let b25 : Bool := (x 7 || (x 13 || false))
  let b26 : Bool := (x 4 && (b21 && true))
  let b27 : Bool := (x 11 || (b25 || false))
  let b28 : Bool := (x 0 && (b27 && true))
  let b29 : Bool := (x 7 || (b19 || false))
  let b30 : Bool := (b24 || (x 13 || false))
  let b31 : Bool := (b28 || (b20 || false))
  let b32 : Bool := (b28 || (x 2 || false))
  let b33 : Bool := (x 3 && (b29 && true))
  let b34 : Bool := (b32 && (b31 && true))
  let b35 : Bool := (x 6 && (b30 && true))
  let b36 : Bool := (x 1 && (b23 && true))
  let b37 : Bool := (b36 || (b22 || false))
  let b38 : Bool := (b33 || (b26 || false))
  let b39 : Bool := (b35 || (b38 || false))
  let b40 : Bool := (b37 || (b39 || false))
  let b41 : Bool := (b40 || (b34 || false))
  change (run gs (List.ofFn x)) = _
  rw [hx]
  unfold gs
  rw [advance ⟨GateOp.or, [12, 7]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14] (by rfl),
    advance ⟨GateOp.or, [13, 8]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15] (by rfl),
    advance ⟨GateOp.or, [12, 11]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16] (by rfl),
    advance ⟨GateOp.or, [9, 16]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17] (by rfl),
    advance ⟨GateOp.or, [11, 8]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18] (by rfl),
    advance ⟨GateOp.or, [9, 10]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19] (by rfl),
    advance ⟨GateOp.or, [15, 9]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20] (by rfl),
    advance ⟨GateOp.or, [10, 18]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21] (by rfl),
    advance ⟨GateOp.and, [5, 17]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22] (by rfl),
    advance ⟨GateOp.or, [14, 8]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23] (by rfl),
    advance ⟨GateOp.or, [12, 10]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24] (by rfl),
    advance ⟨GateOp.or, [7, 13]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25] (by rfl),
    advance ⟨GateOp.and, [4, 21]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26] (by rfl),
    advance ⟨GateOp.or, [11, 25]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27] (by rfl),
    advance ⟨GateOp.and, [0, 27]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28] (by rfl),
    advance ⟨GateOp.or, [7, 19]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29] (by rfl),
    advance ⟨GateOp.or, [24, 13]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30] (by rfl),
    advance ⟨GateOp.or, [28, 20]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31] (by rfl),
    advance ⟨GateOp.or, [28, 2]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32] (by rfl),
    advance ⟨GateOp.and, [3, 29]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33] (by rfl),
    advance ⟨GateOp.and, [32, 31]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34] (by rfl),
    advance ⟨GateOp.and, [6, 30]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35] (by rfl),
    advance ⟨GateOp.and, [1, 23]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36] (by rfl),
    advance ⟨GateOp.or, [36, 22]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37] (by rfl),
    advance ⟨GateOp.or, [33, 26]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38] (by rfl),
    advance ⟨GateOp.or, [35, 38]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39] (by rfl),
    advance ⟨GateOp.or, [37, 39]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40] (by rfl),
    advance ⟨GateOp.or, [40, 34]⟩ _ [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40] [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b34, b35, b36, b37, b38, b39, b40, b41] (by rfl)]
  rfl

theorem valuation (x : Fin 14 → Bool) : cc.eval (List.ofFn x) = form x := by
  change (cc.wires (List.ofFn x)).getD 41 false = _
  rw [wireForm]
  rfl

theorem mono : Monotone2 cc := by
  intro q h
  change q ∈ gs at h
  simp only [gs, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

set_option maxRecDepth 12000 in
theorem pairs : ∀ u v : Fin 14, (u.val,v.val) ∈ ([(0, 7), (1, 7), (3, 7), (1, 8), (2, 8), (4, 8), (2, 9), (3, 9), (5, 9), (3, 10), (4, 10), (6, 10), (4, 11), (5, 11), (0, 11), (5, 12), (6, 12), (1, 12), (6, 13), (0, 13), (2, 13)] : List (ℕ × ℕ)) → (u = 0 ∧ v = 7) ∨ (u = 1 ∧ v = 7) ∨ (u = 3 ∧ v = 7) ∨ (u = 1 ∧ v = 8) ∨ (u = 2 ∧ v = 8) ∨ (u = 4 ∧ v = 8) ∨ (u = 2 ∧ v = 9) ∨ (u = 3 ∧ v = 9) ∨ (u = 5 ∧ v = 9) ∨ (u = 3 ∧ v = 10) ∨ (u = 4 ∧ v = 10) ∨ (u = 6 ∧ v = 10) ∨ (u = 4 ∧ v = 11) ∨ (u = 5 ∧ v = 11) ∨ (u = 0 ∧ v = 11) ∨ (u = 5 ∧ v = 12) ∨ (u = 6 ∧ v = 12) ∨ (u = 1 ∧ v = 12) ∨ (u = 6 ∧ v = 13) ∨ (u = 0 ∧ v = 13) ∨ (u = 2 ∧ v = 13) := by
  intro u v he
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at he
  rcases he with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact (Or.inl ⟨Fin.ext h.1, Fin.ext h.2⟩)
  · exact (Or.inr (Or.inl ⟨Fin.ext h.1, Fin.ext h.2⟩))
  · exact (Or.inr (Or.inr (Or.inl ⟨Fin.ext h.1, Fin.ext h.2⟩)))
  · exact (Or.inr (Or.inr (Or.inr (Or.inl ⟨Fin.ext h.1, Fin.ext h.2⟩))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Fin.ext h.1, Fin.ext h.2⟩)))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Fin.ext h.1, Fin.ext h.2⟩))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Fin.ext h.1, Fin.ext h.2⟩)))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Fin.ext h.1, Fin.ext h.2⟩))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Fin.ext h.1, Fin.ext h.2⟩)))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Fin.ext h.1, Fin.ext h.2⟩))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Fin.ext h.1, Fin.ext h.2⟩)))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Fin.ext h.1, Fin.ext h.2⟩))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Fin.ext h.1, Fin.ext h.2⟩)))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Fin.ext h.1, Fin.ext h.2⟩))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Fin.ext h.1, Fin.ext h.2⟩)))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Fin.ext h.1, Fin.ext h.2⟩))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Fin.ext h.1, Fin.ext h.2⟩)))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Fin.ext h.1, Fin.ext h.2⟩))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Fin.ext h.1, Fin.ext h.2⟩)))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Fin.ext h.1, Fin.ext h.2⟩))))))))))))))))))))
  · exact (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Fin.ext h.1, Fin.ext h.2⟩))))))))))))))))))))

set_option maxHeartbeats 2000000 in
theorem corr (x : Fin 14 → Bool) : form x = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (1, 7), (3, 7), (1, 8), (2, 8), (4, 8), (2, 9), (3, 9), (5, 9), (3, 10), (4, 10), (6, 10), (4, 11), (5, 11), (0, 11), (5, 12), (6, 12), (1, 12), (6, 13), (0, 13), (2, 13)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true := by
  constructor
  · intro y
    simp only [form, Bool.or_false, Bool.and_true, Bool.or_eq_true, Bool.and_eq_true] at y
    rcases y with y | y
    · rcases y with y | y
      · rcases y with y | y
        · rcases y with ⟨ya, yb⟩
          rcases yb with yb | yb
          · rcases yb with yb | yb
            · exact ⟨1, 12, by decide, ya, yb⟩
            · exact ⟨1, 7, by decide, ya, yb⟩
          · exact ⟨1, 8, by decide, ya, yb⟩
        · rcases y with ⟨ya, yb⟩
          rcases yb with yb | yb
          · exact ⟨5, 9, by decide, ya, yb⟩
          · rcases yb with yb | yb
            · exact ⟨5, 12, by decide, ya, yb⟩
            · exact ⟨5, 11, by decide, ya, yb⟩
      · rcases y with y | y
        · rcases y with ⟨ya, yb⟩
          rcases yb with yb | yb
          · rcases yb with yb | yb
            · exact ⟨6, 12, by decide, ya, yb⟩
            · exact ⟨6, 10, by decide, ya, yb⟩
          · exact ⟨6, 13, by decide, ya, yb⟩
        · rcases y with y | y
          · rcases y with ⟨ya, yb⟩
            rcases yb with yb | yb
            · exact ⟨3, 7, by decide, ya, yb⟩
            · rcases yb with yb | yb
              · exact ⟨3, 9, by decide, ya, yb⟩
              · exact ⟨3, 10, by decide, ya, yb⟩
          · rcases y with ⟨ya, yb⟩
            rcases yb with yb | yb
            · exact ⟨4, 10, by decide, ya, yb⟩
            · rcases yb with yb | yb
              · exact ⟨4, 11, by decide, ya, yb⟩
              · exact ⟨4, 8, by decide, ya, yb⟩
    · rcases y with ⟨ya, yb⟩
      rcases ya with ya | ya
      · rcases ya with ⟨yaa, yab⟩
        rcases yab with yab | yab
        · exact ⟨0, 11, by decide, yaa, yab⟩
        · rcases yab with yab | yab
          · exact ⟨0, 7, by decide, yaa, yab⟩
          · exact ⟨0, 13, by decide, yaa, yab⟩
      · rcases yb with yb | yb
        · rcases yb with ⟨yba, ybb⟩
          rcases ybb with ybb | ybb
          · exact ⟨0, 11, by decide, yba, ybb⟩
          · rcases ybb with ybb | ybb
            · exact ⟨0, 7, by decide, yba, ybb⟩
            · exact ⟨0, 13, by decide, yba, ybb⟩
        · rcases yb with yb | yb
          · rcases yb with yb | yb
            · exact ⟨2, 13, by decide, ya, yb⟩
            · exact ⟨2, 8, by decide, ya, yb⟩
          · exact ⟨2, 9, by decide, ya, yb⟩
  · rintro ⟨u,v,he,hu,hv⟩
    rcases pairs u v he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals simp [form, hu, hv]

theorem edgeFrom : ∀ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) → ((Fin.castAdd 7 p).val,(Fin.natAdd 7 l).val) ∈ ([(0, 7), (1, 7), (3, 7), (1, 8), (2, 8), (4, 8), (2, 9), (3, 9), (5, 9), (3, 10), (4, 10), (6, 10), (4, 11), (5, 11), (0, 11), (5, 12), (6, 12), (1, 12), (6, 13), (0, 13), (2, 13)] : List (ℕ × ℕ)) := by
  decide +kernel

theorem right (x : Fin 14 → Bool) : cc.eval (List.ofFn x) = true ↔ ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true := by
  rw [valuation, corr]
  constructor
  · rintro ⟨u,v,he,hu,hv⟩
    rcases pairs u v he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨0, 0, by decide, hu, hv⟩
    · exact ⟨1, 0, by decide, hu, hv⟩
    · exact ⟨3, 0, by decide, hu, hv⟩
    · exact ⟨1, 1, by decide, hu, hv⟩
    · exact ⟨2, 1, by decide, hu, hv⟩
    · exact ⟨4, 1, by decide, hu, hv⟩
    · exact ⟨2, 2, by decide, hu, hv⟩
    · exact ⟨3, 2, by decide, hu, hv⟩
    · exact ⟨5, 2, by decide, hu, hv⟩
    · exact ⟨3, 3, by decide, hu, hv⟩
    · exact ⟨4, 3, by decide, hu, hv⟩
    · exact ⟨6, 3, by decide, hu, hv⟩
    · exact ⟨4, 4, by decide, hu, hv⟩
    · exact ⟨5, 4, by decide, hu, hv⟩
    · exact ⟨0, 4, by decide, hu, hv⟩
    · exact ⟨5, 5, by decide, hu, hv⟩
    · exact ⟨6, 5, by decide, hu, hv⟩
    · exact ⟨1, 5, by decide, hu, hv⟩
    · exact ⟨6, 6, by decide, hu, hv⟩
    · exact ⟨0, 6, by decide, hu, hv⟩
    · exact ⟨2, 6, by decide, hu, hv⟩
  · rintro ⟨p,l,h,hp,hl⟩
    exact ⟨Fin.castAdd 7 p,Fin.natAdd 7 l,edgeFrom p l h,hp,hl⟩

end Fano2348Control

attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
set_option maxRecDepth 12000 in
set_option maxHeartbeats 1600000 in
theorem Fano2348Control.negated_bound : ¬ (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (28 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.or →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (∀ (x7 : Bool),                 ∃ (x8 : ℕ → Bool),                   have x9 : List Bool := x1.wires (List.ofFn fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = if x7 = Bool.true then (0 : Fin (14 : ℕ)) else (7 : Fin (14 : ℕ))));                   (∀ x10 < (14 : ℕ), x8 x10 = Decidable.decide (x10 = if x7 = Bool.true then (7 : ℕ) else (0 : ℕ))) ∧                     (∀ x10 < x1.size,                         have x12 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10;                         have x13 : ℕ := PEqualNP.TopForm.opnd x1 x10 (0 : Fin (2 : ℕ));                         have x14 : ℕ := PEqualNP.TopForm.opnd x1 x10 (1 : Fin (2 : ℕ));                         (x12.op = PEqualNP.CircuitLowerBounds.GateOp.and → x8 ((14 : ℕ) + x10) = (x9.getD x13 Bool.false && x8 x14 || x8 x13 && x9.getD x14 Bool.false)) ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or → x8 ((14 : ℕ) + x10) = (x8 x13 || x8 x14))) ∧                       x8 x1.output = Bool.false) →               False) := by
  intro contra
  apply contra Fano2348Control.cc (by decide) (by decide +kernel) (by decide +kernel) (by rfl)
  · exact Fano2348Control.right
  · intro b
    cases b
    · refine ⟨fun w => Nat.testBit 6710886401 w, ?_⟩
      dsimp only
      rw [Fano2348Control.wireForm]
      decide +kernel
    · refine ⟨fun w => Nat.testBit 7423934592 w, ?_⟩
      dsimp only
      rw [Fano2348Control.wireForm]
      decide +kernel

#print axioms Fano2348Control.negated_bound
