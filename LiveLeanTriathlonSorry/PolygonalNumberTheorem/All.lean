/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
import Mathlib.Tactic.Attr.Register
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Tactic.Rify
public import LiveLeanTriathlonSorry.Util.Attributes
@[expose] public section

section Main

def pol_num (m : ℤ) (k : ℤ) := m * k * (k - 1) / 2 + k

theorem polygonal_number_theorem_even (m N : ℤ) (hm1 : m ≥ 3) (hN : N ≥ 28 * m ^ 3) (hm2 : Even m) :
    ∃ (k1 k2 k3 k4 : ℤ), N = pol_num m k1 + pol_num m k2 + pol_num m k3 + pol_num m k4 ∨ N =
    pol_num m k1 + pol_num m k2 + pol_num m k3 + pol_num m k4 + 1 := by sorry

end Main
