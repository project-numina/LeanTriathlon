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

def TwinPrimes : Set ℕ :=
  {p | p.Prime ∧ (p + 2).Prime}

open Classical in

@[AMS 11]
theorem brun : Summable (fun n ↦ if n ∈ TwinPrimes then 1 / (n : ℝ) else 0) := by sorry

end Main
