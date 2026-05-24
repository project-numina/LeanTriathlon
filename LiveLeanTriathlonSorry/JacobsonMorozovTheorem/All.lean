/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib
public import LiveLeanTriathlonSorry.Mathlib.Algebra.Lie.CartanCriterion
public import LiveLeanTriathlonSorry.Mathlib.RingTheory.Finiteness.Nilpotent
public import LiveLeanTriathlonSorry.Mathlib.LinearAlgebra.Eigenspace.Zero
public import LiveLeanTriathlonSorry.Util.Attributes
@[expose] public section

section Main

variable (L : Type*) [LieRing L] [LieAlgebra ℂ L]

@[AMS 17]
theorem Jacobson_Morozov (x : L) [FiniteDimensional ℂ L] [hL : LieAlgebra.IsSemisimple ℂ L]
    (hx0 : x ≠ 0) (hx : IsNilpotent (LieAlgebra.ad ℂ L x)) : ∃ h y : L, IsSl2Triple h x y := by sorry

end Main
