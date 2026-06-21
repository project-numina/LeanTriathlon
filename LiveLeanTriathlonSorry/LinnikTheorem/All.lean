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

/--
The least prime in the progression a, a + d, a + 2d, ... (or zero if no such prime exists).
-/
noncomputable def p (a d : ℕ) : ℕ := sInf ({a + k * d | k : ℕ} ∩ {p | p.Prime})

@[AMS 11]
theorem linnik : ∃ c L : ℝ, ∀ ⦃a d : ℕ⦄,
      0 < a → a < d → a.Coprime d → p a d ≤ c * (↑d : ℝ) ^ L := by sorry

end Main
