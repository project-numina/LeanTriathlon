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

open Nat Set

@[AMS 11]
theorem ramanujan_nagell (n : ℕ) (hn : 3 ≤ n):
    (∃ x, 2 ^ n - 7 = x ^ 2) ↔ n ∈ ({3, 4, 5, 7, 15} : Set ℕ) := by sorry

end Main
