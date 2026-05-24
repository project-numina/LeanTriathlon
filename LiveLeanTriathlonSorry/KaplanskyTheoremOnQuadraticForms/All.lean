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

@[AMS 11]
theorem kaplansky_two {p : ℕ} (hp : p.Prime) (hp' : p ≡ 9 [MOD 16]) :
    ∃! t, (t = 32 ∨ t = 64) ∧ ∃ x y : ℕ, p = x ^ 2 + t * y ^ 2 := by sorry

end Main
