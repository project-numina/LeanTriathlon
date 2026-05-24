/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Bolton Bailey, ...
-/

module
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import LiveLeanTriathlonSorry.Mathlib.Data.Set.Lattice
public import LiveLeanTriathlonSorry.Mathlib.Topology.Connected.Basic
public import LiveLeanTriathlonSorry.Util.Attributes
@[expose] public section

section Main

open Real Set Pointwise MeasureTheory

section BackgroundLemmas

end BackgroundLemmas

section MainTheorem

@[AMS 28]
theorem exists_Ioo_subset_diff_self_of_measure_pos {A : Set ℝ}
    (A_mble : MeasurableSet A) (A_pos : 0 < volume A) :
    ∃ δ > 0, Ioo (-δ) δ ⊆ A - A := by sorry

end MainTheorem

end Main
