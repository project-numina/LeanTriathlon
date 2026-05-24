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

open scoped Classical ArithmeticFunction.omega

noncomputable def stdNormalCDF (z : ℝ) : ℝ :=
  ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) z

noncomputable def normalizedOmega (n : ℕ) : ℝ :=
  let ll := Real.log (Real.log (n : ℝ))
  ((ω n : ℝ) - ll) / Real.sqrt ll

@[AMS 11]
theorem erdos_kac (a b : ℝ) (hab : a < b) :
    Filter.Tendsto
      (fun N : ℕ =>
        ((Finset.Icc 1 N |>.filter fun n =>
            a ≤ normalizedOmega n ∧ normalizedOmega n ≤ b).card : ℝ) / (N : ℝ))
      Filter.atTop
      (nhds (stdNormalCDF b - stdNormalCDF a)) := by sorry

end Main
