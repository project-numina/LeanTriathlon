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

def IsPrimitivePrimeDivisor (a b n p : Nat) : Prop :=
  Nat.Prime p
    ∧ p ∣ a ^ n - b ^ n
    ∧ ∀ k : Nat, 1 ≤ k → k < n → ¬(p ∣ a ^ k - b ^ k)

@[AMS 11]
theorem zsigmondy_theorem
    (a b n : Nat)
    (hab_coprime : Nat.Coprime a b)
    (ha_gt_b : b < a)
    (hb_pos : 0 < b)
    (hn : 2 ≤ n)
    (hexc1 : ¬(n = 2 ∧ (a + b).isPowerOfTwo))
    (hexc2 : ¬(a = 2 ∧ b = 1 ∧ n = 6)) :
    ∃ p, IsPrimitivePrimeDivisor a b n p := by sorry

end Main
