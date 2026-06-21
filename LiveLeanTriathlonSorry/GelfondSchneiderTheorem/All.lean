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

open Set Function

universe u
@[AMS 11]

theorem gelfond_schneider (a b : ℝ) (ha_pos : 0 < a) (ha_neq : a ≠ 1)
    (ha_alg : IsAlgebraic ℚ a) (hb_alg : IsAlgebraic ℚ b) (hb : Irrational b) :
    Transcendental ℚ (a ^ b) := by sorry

end Main