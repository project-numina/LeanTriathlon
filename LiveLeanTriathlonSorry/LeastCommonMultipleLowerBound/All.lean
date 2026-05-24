/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
import Mathlib.Tactic.Attr.Register
public import LiveLeanTriathlonSorry.Util.Attributes
public import LiveLeanTriathlonSorry.Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import LiveLeanTriathlonSorry.Mathlib.Data.Nat.Div.Basic
public import LiveLeanTriathlonSorry.Mathlib.Data.Nat.Lcm
@[expose] public section

section Main

@[AMS 11]
theorem Nat.LCM_lower_bound (n : ℕ) (hn : 7 ≤ n) : 2 ^ n ≤ LCM n := sorry

end Main
