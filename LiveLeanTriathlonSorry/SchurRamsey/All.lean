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

open Setoid Set

@[AMS 05]
theorem schur (n : ℕ) : ∃ S : ℕ, ∀ r : (Icc 1 S) → Fin n,
    ∃ u : Fin n,
        ∃ x y z : Icc 1 S,
            r x = u ∧ r y = u ∧ r z = u ∧ (x : ℕ) + y = z := by sorry

end Main
