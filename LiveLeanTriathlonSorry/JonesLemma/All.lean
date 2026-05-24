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

open TopologicalSpace Cardinal Set

@[AMS 54]
theorem jones {X : Type*} [TopologicalSpace X] [SeparableSpace X] [NormalSpace X] {Y : Set X}
    (hc : IsClosed Y) (hd : IsDiscrete Y) : 2 ^ #Y ≤ 𝔠 := by sorry

end Main
