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

-- Needed for def

@[AMS 14]
theorem NagellLutz1 {E : WeierstrassCurve.Affine ℚ}
    (h1 : E.IsIntegral ℤ) (h2 : E.Δ ≠ 0) {x y : ℚ} (h : E.Nonsingular x y)
    (hx : 0 < addOrderOf (WeierstrassCurve.Affine.Point.some x y h)) :
    x ∈ (algebraMap ℤ ℚ).range ∧ y ∈ (algebraMap ℤ ℚ).range := sorry

@[AMS 14]
theorem NagellLutz2 {E : WeierstrassCurve.Affine ℚ}
    (h1 : E.IsIntegral ℤ)
    (h2 : E.Δ ≠ 0) {x y : ℚ} (h : E.Nonsingular x y)
    (hx : 0 < addOrderOf (WeierstrassCurve.Affine.Point.some x y h)) :
    (y = 0 ∧ addOrderOf (WeierstrassCurve.Affine.Point.some x y h) = 2) ∨
    (NagellLutz1 h1 h2 h hx).2.choose ^ 2 ∣ (E.Δ_integral_of_isIntegral ℤ).choose := sorry

end Main
