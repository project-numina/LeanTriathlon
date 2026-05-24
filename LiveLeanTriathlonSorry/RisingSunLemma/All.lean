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

open Set TopologicalSpace Real

variable {a b : ℝ} {g : ℝ → ℝ}

def Shadow (a b : ℝ) (g : ℝ → ℝ) : Set ℝ :=
  {x ∈ Icc a b | ∃ y ∈ Icc a b, x < y ∧ g x < g y}

def E (a b : ℝ) (g : ℝ → ℝ) : Set ℝ :=
  Ioo a b ∩ Shadow a b g

@[AMS 26]
theorem risingsun {a b : ℝ} (ab : a < b) {g : ℝ → ℝ} (hg : Continuous g) :
    ∃ k : ℕ → ℝ × ℝ, ∀ i j : ℕ, i ≠ j → Ioo (k i).1 (k i).2 ∩ Ioo (k j).1 (k j).2 = ∅
      ∧ E a b g = ⋃ n : ℕ, Ioo (k n).1 (k n).2
      ∧ (∀ n : ℕ, (k n).1 ≠ a → g (k n).1 = g (k n).2)
      ∧ (∀ n : ℕ, (k n).1 = a → a ∈ Shadow a b g → g a < g (k n).2)
      ∧ (∀ n : ℕ, ∀ x : ℝ, x ∈ Ioo (k n).1 (k n).2 → g x < g (k n).2) := by sorry

end Main
