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

noncomputable def d : ℕ → ℕ → ℕ := fun a b ↦ sInf ({a + k * b | k : ℕ} ∩ {p | p.Prime})

@[AMS 11]
theorem linnik : ∃ c L : ℝ, ∀ ⦃a b : ℕ⦄, a.Coprime b → d a b ≤ c * (↑b : ℝ) ^ L := by sorry

end Main
