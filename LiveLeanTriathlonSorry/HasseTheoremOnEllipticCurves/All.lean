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

@[AMS 11]
theorem HasseBound (F : Type*) [Finite F] [Field F] (E : WeierstrassCurve.Affine F) :
    abs ((Nat.card <| E.Point : ℝ) - (Nat.card F + 1)) ≤ 2 * Real.sqrt (Nat.card F) := sorry

end Main
