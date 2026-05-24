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

open FirstOrder FirstOrder.Language FirstOrder.Ring
noncomputable section

instance : Language.ring.Structure ℚ := (compatibleRingOfRing ℚ).toStructure

@[AMS 03]
theorem nat_definable_in_rat :
    (∅ : Set ℚ).Definable₁ Language.ring (Set.range (Nat.cast : ℕ → ℚ)) := by sorry

end

end Main
