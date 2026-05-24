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

noncomputable def A002326 (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ (2 * n + 1) ∣ 2 ^ m - 1}

noncomputable abbrev a := A002326

noncomputable def A179382 : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 1 => ∑ j ∈ Finset.range (a n), (2 ^ j % (2 * n + 1)) % 2

noncomputable abbrev b := A179382

@[AMS 11]
theorem smallest_period_div {n : ℕ} (hn : 0 < n) :
    (↑(b (n + 1)) : ℝ) = (2 * n + 1 : ℝ)⁻¹ * ∑ j ∈ Finset.range (a n), (2 ^ j % (2 * n + 1)) := by sorry

end Main
