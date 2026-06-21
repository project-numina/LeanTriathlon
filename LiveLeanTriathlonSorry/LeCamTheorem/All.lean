/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib
public import LiveLeanTriathlonSorry.Util.Attributes
@[expose] public section

section Main

noncomputable def independentSum {α : Type} [AddMonoid α] : List (PMF α) → PMF α
  | [] => PMF.pure 0
  | X :: XS => do
    let x ← X
    let y ← independentSum XS
    pure (x + y)

noncomputable def PMF.bernoulliNat_of_unitInterval (p : unitInterval) : PMF ℕ := do
  let x ← PMF.bernoulli p.val.toNNReal (by simp; grind)
  pure (if x = 0 then 0 else 1)

@[AMS 60]
theorem LeCamTheorem (ps : List unitInterval) (hps : ∀ p ∈ ps, 0 ≤ p ∧ p ≤ 1) :
  let mean := (ps.map (fun p => p.val)).sum
  let sum := independentSum (ps.map (fun k => PMF.bernoulliNat_of_unitInterval (k) ) )
  ∑' k : ℕ,
    |(sum k).toReal - (Real.exp (-mean) * mean ^ k / k.factorial)| ≤ 2 * (ps.map (fun p => p.val ^ 2)).sum := sorry

end Main
