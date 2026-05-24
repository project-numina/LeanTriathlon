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

@[AMS 11]
theorem Nat.Prime.greenTao (k : ℕ) :
    ∃ a d : ℕ, 0 < d ∧ ∀ i < k, (a + i * d).Prime := by sorry

end Main
