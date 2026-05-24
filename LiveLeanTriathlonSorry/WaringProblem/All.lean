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
theorem waring (n : ℕ) : ∃ t : ℕ,
    ∀ k, ∃ s : Finset ℕ, s.card ≤ t ∧ k = ∑ i ∈ s, i ^ n := by sorry

end Main
