/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib
public import LiveLeanTriathlonSorry.Util.Attributes
public import LiveLeanTriathlonSorry.Mathlib.LinearAlgebra.Matrix.QuadraticForm
@[expose] public section

section Main
noncomputable section

def critical_290_numbers : Finset ℕ :=
  {1, 2, 3, 5, 6, 7, 10, 13, 14, 15, 17, 19, 21, 22, 23, 26, 29, 30, 31,
   34, 35, 37, 42, 58, 93, 110, 145, 203, 290}

@[AMS 11]
theorem two_ninety_theorem {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hpos : M.PosDef)
    (hIntegral : M.Integral)
    (hrep : ∀ m ∈ critical_290_numbers, M.TakesValue m) :
    M.Universal := by sorry

end

end Main
