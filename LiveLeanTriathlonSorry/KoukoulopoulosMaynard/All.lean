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

open MeasureTheory Set Nat

@[AMS 11]
theorem koukoulopoulos_maynard {f : ℕ → ℝ} (hf : ∀ n, 0 < f n) :
    (∀ᵐ (x : ℝ), {(p, q) : ℕ × ℕ | p.Coprime q ∧ |x - p / (↑q : ℝ)|
      < f q / (↑q : ℝ)}.Finite) ↔ Summable fun n ↦ φ n * f n / (↑n : ℝ) := sorry

end Main
