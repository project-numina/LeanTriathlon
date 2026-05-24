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

open Nat

structure DominoTiling (s : Set (ℤ × ℤ)) where
  f : s → s
  inv : f^[2] = id
  tilt : ∀ x : s, |(f x).val.1 - x.val.1| + |(f x).val.2 - x.val.2| = 1

def AztecDiamond (n : ℕ) : Set (ℤ × ℤ) :=
  {x : ℤ × ℤ | |(↑x.1 : ℝ) - 0.5| + |(↑x.2 : ℝ) - 0.5| ≤ n}

@[AMS 05]
theorem aztecDiamond_tiling (n : ℕ) :
    Nat.card (DominoTiling (AztecDiamond n)) = 2 ^ ((n + 1).choose 2) := by sorry

end Main
