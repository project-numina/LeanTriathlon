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

open ArithmeticFunction.sigma Real

@[AMS 11]
theorem robin : RiemannHypothesis ↔ ∀ n > 5040,
    σ 1 n < exp (eulerMascheroniConstant) * n * log (log n) := by sorry

end Main
