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

open Function Set

@[AMS 30]
theorem picard {f : ℂ → ℂ} (f_diff : Differentiable ℂ f) (f_ne_const : ∀ a : ℂ, ∃ b : ℂ, f b ≠ a) :
    ∃ x : ℂ, {x}ᶜ ⊆ range f := by sorry

end Main
