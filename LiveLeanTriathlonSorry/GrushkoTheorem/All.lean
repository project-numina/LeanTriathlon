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

open Group Monoid.Coprod

instance grushko' {G H : Type*} [Group G] [Group H] [FG G] [FG H] : FG (G ∗ H) := sorry

@[AMS 20]
theorem grushko {G H : Type*} [Group G] [Group H] [FG G] [FG H] :
  rank (G ∗ H) = rank G + rank H := by sorry

end Main
