import PEqualNP.MetaComplexity.Helpers.PermInputs
import PEqualNP.MetaComplexity.Helpers.LocalPrivate2

namespace FanoMixedSize
open PEqualNP.MetaComplexity

/-- Each input may be replaced by a raw wire or by false without adding a gate. -/
theorem optional_projection {n m s : ℕ} (pick : Fin n → Option (Fin m))
    (f : (Fin n → Bool) → Bool) (hc : HasCircuitSize n f s) :
    HasCircuitSize m (fun x => f (fun i => (pick i).elim false x)) s := by
  let π : Fin n → Fin (m+1) := fun i => (pick i).elim (Fin.last m) Fin.castSucc
  have h := Helpers.PermInputs.relabel_size π f s hc
  have h' := Helpers.LocalPrivate2.fix_false m s _ h
  suffices e : (fun y : Fin m → Bool => f (Fin.snoc y false ∘ π)) =
      (fun y => f (fun i => (pick i).elim false y)) by rwa [e] at h'
  funext y
  congr 1
  funext i
  cases hpi : pick i <;> simp [Function.comp_apply, π, hpi]

#print axioms optional_projection
end FanoMixedSize
