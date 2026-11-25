import PEqualNP.Defs


set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem FiveVertexChild : ∃ (op : Fin 6 → Bool) (a b : Fin 6 → Fin 33)
        (s : ℕ → ℕ) (d : Fin 1 → Fin 6) (q : Fin 1 → Fin 24),
      (∀ i : Fin 11, s i.val = ([2147418115, 663661903884, 34144976944, 728266375360, 21653750532, 103293914128, 26322415680, 344922804352, 414195942664, 581968119809, 1065151898146] : List ℕ).getD i.val 0) ∧
      (∀ i, (a i).val ∈ ([3, 6, 7, 9, 10] : List ℕ) ∨ 25 ≤ (a i).val) ∧
      (∀ i, (b i).val ∈ ([3, 6, 7, 9, 10] : List ℕ) ∨ 25 ≤ (b i).val) ∧
      (∀ i, (a i).val < 25+i.val ∧ (b i).val < 25+i.val ∧
        s (25+i.val) = if op i = true then s (a i).val &&& s (b i).val else s (a i).val ||| s (b i).val) ∧
      s 30 = 28864 ∧ Function.Injective d ∧
      ∀ i, op (d i) = true ∧ (s (25+(d i).val)).testBit (16+(q i).val) = true := by
  refine ⟨(fun i => ([false,false,false,true,false,true] : List Bool).getD i.val false),
    (fun i => ([6,7,6,25,3,27] : List (Fin 33)).getD i.val 0),
    (fun i => ([9,10,7,26,28,29] : List (Fin 33)).getD i.val 0),
    (fun j => ([2147418115,663661903884,34144976944,728266375360,21653750532,103293914128,26322415680,344922804352,414195942664,581968119809,1065151898146,0,0,0,0,0,0,0,0,0,0,0,0,0,0,582520731713,1066477318818,371245215936,549755842560,728266404032,28864] : List ℕ).getD j 0),
    (fun i => ([3] : List (Fin 6)).getD i.val 0),
    (fun i => ([23] : List (Fin 24)).getD i.val 0), ?_⟩
  exact ⟨by decide, by decide, by decide, by decide, rfl, by unfold Function.Injective; decide, by decide⟩
#print axioms FiveVertexChild

