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

open Set Function MeasureTheory

@[AMS 26]
theorem lusin {a b ε : ℝ} (ab : a < b) {f : ℝ → ℂ} (f_meas : Measurable f) (εp : 0 < ε) :
    ∃ E ⊆ Icc a b, IsCompact E ∧ Continuous (restrict E f) ∧ b - a - ε < (volume E).toReal := by sorry

end Main
