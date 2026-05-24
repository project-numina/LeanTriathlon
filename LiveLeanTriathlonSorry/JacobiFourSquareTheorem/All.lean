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
theorem jacobi (n : ℕ) : {a : Fin 4 → ℤ | (↑n : ℤ) = ∑ i : Fin 4, a i}.ncard
    = 8 * ∑' m : {m : ℕ | m ∣ n ∧ ¬ 4 ∣ m}, m.val := by sorry

end Main
