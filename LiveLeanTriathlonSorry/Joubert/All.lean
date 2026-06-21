/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib.FieldTheory.SeparableClosure
public import LiveLeanTriathlonSorry.Util.Attributes
@[expose] public section

section Main

open Polynomial

@[AMS 12]
theorem exists_generator_of_minpoly_with_some_zero_coeffs (K L : Type*)
    [Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L] (h2 : (2 : K) ≠ 0)
    (h : Field.sepDegree K L = 6) :
  ∃ a : L, Algebra.adjoin K {a} = ⊤ ∧
  (∃ c4 c2 c1 c0 : K, minpoly K a = X ^ 6 + C c4 * X ^ 4 + C c2 * X ^ 2 + C c1 * X + C c0) := by sorry

end Main
