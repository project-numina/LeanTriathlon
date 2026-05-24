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

open Real

@[AMS 30]
theorem carlson {f : ℂ → ℂ} (f_diff : Differentiable ℂ f)
    (f_bound : ∃ C t : ℝ, ∀ x : ℂ, ‖f x‖ ≤ C * rexp (t * ‖x‖))
    (f_bound' : ∃ C c : ℝ, c < π ∧ ∀ x : ℝ, ‖f (.I * x)‖ ≤ C * rexp (c * |x|))
    (f_nat : ∀ n : ℕ, f n = 0): f = 0 := by sorry

end Main
