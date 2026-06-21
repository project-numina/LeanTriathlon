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

open Polynomial Nat

@[AMS 11]
theorem lagrange {p : ℕ} (hp : p.Prime) {f : Polynomial ℤ} (h : ∃ n : ℕ, ¬ (↑p : ℤ) ∣ f.coeff n):
    {n : ℕ | n < p ∧ ↑p ∣ eval (↑n : ℤ) f}.ncard ≤ f.natDegree := sorry

end Main
