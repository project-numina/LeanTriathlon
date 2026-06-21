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
theorem waring (n : ℕ) (hn : 0 < n) : ∃ t : ℕ,
    ∀ k, ∃ s : Multiset ℕ, s.card ≤ t ∧ k = (s.map fun i => i ^ n).sum := by sorry

end Main
