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

open Metric

abbrev UnitNDimensionalSphere (n : ℕ) := sphere (0 : (Fin (n + 1) → ℝ)) 1

@[AMS 54]
theorem borsuk_ulam (n : ℕ) {g : UnitNDimensionalSphere n → Fin n → ℝ}
    (hg : ∀ x : UnitNDimensionalSphere n, g (-x) = g x) (cont : Continuous g):
    ∃ x : UnitNDimensionalSphere n, g x = 0 := by sorry

end Main
