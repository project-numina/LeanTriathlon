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

universe u

def IsProth (n : ℕ) : Prop :=
  ∃ k a : ℕ, Odd k ∧ k < 2 ^ a ∧ n = k * 2 ^ a + 1

@[AMS 11]
theorem proth {n : ℕ} (h : IsProth n) : n.Prime ↔ ∃ a : ℕ, a ^ ((n - 1) / 2) ≡ -1 [ZMOD n] := by sorry

end Main
