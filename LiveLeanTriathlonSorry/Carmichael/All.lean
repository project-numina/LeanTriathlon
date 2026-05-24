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

open Nat Int

def U (p q : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => p * U p q (n + 1) + q * U p q n

@[AMS 11]
theorem carmichael {p q : ℤ} {n : ℕ}
    (hn : n ∉ ({1, 2, 6} : Set ℕ))
    (hn12 : n ≠ 12 ∨ (p ≠ 1 ∧ p ≠ -1) ∨ q ≠ -1)
    (hpq : IsCoprime p q)
    (hpq_disc : 0 < p ^ 2 - 4 * q)
    (hpq' : p ≠ 0) (hq : q ≠ 0) :
    (∃ r : ℕ, r.Prime ∧ (↑r : ℤ) ∣ U p q n ∧ ∀ m < n, ¬ (↑r : ℤ) ∣ U p q m ) := by sorry

end Main
