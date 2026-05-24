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

open Metric NNReal

@[AMS 54]
theorem caristi {X : Type*} [MetricSpace X] [CompleteSpace X] {T : X → X} {f : X → ℝ≥0}
    (hf : LowerSemicontinuous f) (h : ∀ x : X, dist x (T x) ≤ f x - f (T x)) :
    ∃ x : X, T x = x := by sorry

end Main
