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

open Filter Nat

@[AMS 11]
theorem chen : ∀ᶠ n in atTop, ∃ a b : ℕ,
    2 * n = a + b ∧ a.Prime ∧ 1 < b ∧ b.primeFactorsList.length ≤ 2 := by sorry

end Main
