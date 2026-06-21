/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib
public import LiveLeanTriathlonSorry.Util.Attributes
public import LiveLeanTriathlonSorry.Mathlib.Data.ENNReal.Operations
@[expose] public section

section Main

open ENNReal NNReal Set

noncomputable def IrrationalityMeasure (x : ℝ) : ℝ≥0∞ :=
  sSup (ENNReal.ofNNReal '' {r : ℝ≥0 | LiouvilleWith r.toReal x})

theorem irrationalityMeasure_of_liouville {x : ℝ} (hx : Liouville x) :
      IrrationalityMeasure x = ⊤ := by sorry

theorem irrationalityMeasure_ge_one (x : ℝ) :
      1 ≤ IrrationalityMeasure x := by sorry

@[AMS 11]
theorem roth {x : ℝ} (hx_irr : Irrational x) (hx_alg : IsAlgebraic ℚ x) :
    IrrationalityMeasure x = 2 := sorry

end Main
