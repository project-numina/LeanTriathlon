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

open Nat Set Real

def PrimesLe (n : ℕ) : Finset ℕ := (Finset.Icc 0 n).filter Nat.Prime

@[AMS 11]
theorem merten_first {n : ℕ} (hn : 2 ≤ n) :
  |- Real.log n + ∑ k ∈ PrimesLe n, Real.log k / k| ≤ 2 := by sorry

end Main
