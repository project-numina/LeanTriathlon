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

@[AMS 52]
theorem tverberg (d r : ℕ) (d_pos : 0 < d) (r_pos : 0 < r)
    (S : Finset (EuclideanSpace ℝ (Fin d))) (hS : S.card = (d + 1) * (r - 1) + 1) :
    ∃ (x : EuclideanSpace ℝ (Fin d)) (partition : Finpartition S),
      partition.parts.card = r ∧
      ∀ part ∈ partition.parts, x ∈ convexHull ℝ part := by sorry

end Main
