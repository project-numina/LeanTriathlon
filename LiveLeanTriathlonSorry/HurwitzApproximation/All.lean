/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Algebra.ContinuedFractions.Determinant
public import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Tactic.Attr.Register
public import LiveLeanTriathlonSorry.Util.Attributes
@[expose] public section

section Main

open Real GenContFract Set
noncomputable section

@[AMS 11]
theorem hurwitz_approximation (ξ : ℝ) (hξ : Irrational ξ) :
    { q : ℚ | |ξ - q| < 1 / (sqrt 5 * q.den ^ 2) }.Infinite := by sorry

end

end Main
