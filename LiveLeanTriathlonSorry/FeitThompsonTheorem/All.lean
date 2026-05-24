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

open Set Function Nat

universe u

@[AMS 20]
theorem feit_thompson {G : Type u} [Fintype G] [Group G] (h : Odd (Fintype.card G)) :
    IsSolvable G := by sorry

end Main
