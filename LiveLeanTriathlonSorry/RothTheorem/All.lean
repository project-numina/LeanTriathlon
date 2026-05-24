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

open ENNReal Set

noncomputable def IrrationalityMeasure (x : ℝ) : ℝ≥0∞ :=
  sSup {r : ℝ≥0∞ | LiouvilleWith r.toReal x}

@[AMS 11]
theorem roth {x : ℝ} (hx_irr : Irrational x) (hx_alg : IsAlgebraic ℚ x) :
    IrrationalityMeasure x = 2 := sorry

end Main
