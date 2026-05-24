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

universe u

class Pythagorean (R : Type u) [Semiring R] : Prop where
  sum_sq : ∀ a b : R, IsSquare (a ^ 2 + b ^ 2)

@[AMS 12]
theorem diller_dress (K L : Type*) [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    [Pythagorean L] : Pythagorean K := by sorry

end Main
