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

open scoped EuclideanGeometry

structure Line2 where
  toAffineSubspace : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))
  nonempty : (toAffineSubspace : Set (EuclideanSpace ℝ (Fin 2))).Nonempty
  dim_one : Module.finrank ℝ toAffineSubspace.direction = 1

instance : Membership (EuclideanSpace ℝ (Fin 2)) Line2 where
  mem (l : Line2) (p : EuclideanSpace ℝ (Fin 2)) := p ∈ l.toAffineSubspace

open Classical in
noncomputable def incidenceCount
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : Finset Line2) : ℕ :=
  ((P ×ˢ L).filter fun pl => pl.1 ∈ pl.2.toAffineSubspace).card

@[AMS 52]
theorem szemeredi_trotter :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset (EuclideanSpace ℝ (Fin 2)))
      (L : Finset Line2),
      (incidenceCount P L : ℝ) ≤
        C * ((P.card : ℝ) ^ ((2 : ℝ) / 3) *
             (L.card : ℝ) ^ ((2 : ℝ) / 3) +
             (P.card : ℝ) + (L.card : ℝ)) := by sorry

end Main
