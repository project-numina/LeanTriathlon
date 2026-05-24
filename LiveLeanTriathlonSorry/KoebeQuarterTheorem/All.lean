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

open Set Metric

@[AMS 30]
theorem koebe {f : ℂ → ℂ} (f_inj : InjOn f (ball 0 1)) (f_diff : DifferentiableOn ℂ f (ball 0 1)) :
   ball (f 0) (‖deriv f 0‖ / 4) ⊆ f '' (ball 0 1) := by sorry

end Main
