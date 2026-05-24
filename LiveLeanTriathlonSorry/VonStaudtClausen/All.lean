/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib
public import LiveLeanTriathlonSorry.Mathlib.Data.ZMod.Basic
public import LiveLeanTriathlonSorry.Mathlib.RingTheory.Localization.Integer
public import LiveLeanTriathlonSorry.Util.Attributes
public import LiveLeanTriathlonSorry.Mathlib.Logic.IsEmpty
@[expose] public section

section Main

@[AMS 11]
theorem von_staudt_clausen (n : ℕ) (hn : 1 ≤ n) :
    IsLocalization.IsInteger ℤ (bernoulli (2 * n) + ∑ j ∈ (Finset.range (2 * n + 1)).filter
    (fun j => (j + 1).Prime) , if j ∣ (2 * n) then (1 : ℚ) / (j+1) else 0) := by sorry

end Main
