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

open Set Filter Asymptotics

def IsSumFree {R : Type*} [Add R] (s : Set R) : Prop :=
  ∀ᵉ (a ∈ s) (b ∈ s) (c ∈ s), a + b ≠ c

@[AMS 05]
theorem cameron_erdos :
    (fun (n : ℕ) ↦ (↑{s : Set ℕ | s ⊆ Finset.range n ∧ IsSumFree s}.ncard : ℝ))
    =O[atTop] (fun (n : ℕ) ↦ (2 : ℝ) ^ ((↑n : ℝ) / 2)) := by sorry

end Main
