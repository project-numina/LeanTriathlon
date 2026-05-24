/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.Geometry.Euclidean.Triangle
public import LiveLeanTriathlonSorry.Util.Attributes
@[expose] public section

section Main

open Real EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

@[AMS 51]
theorem hinge_iff_geometric (A B₁ B₂ C₁ C₂ : P)
    (hab₁ : dist A B₁ = dist A B₂)
    (hac₁ : dist A C₁ = dist A C₂)
    (hb₁c₁ : B₁ ≠ C₁) (hb₂c₂ : B₂ ≠ C₂)
    (hab₁_ne : A ≠ B₁) (hac₁_ne : A ≠ C₁) :
    angle B₁ A C₁ > angle B₂ A C₂ ↔ dist B₁ C₁ > dist B₂ C₂ := by sorry

end Main
