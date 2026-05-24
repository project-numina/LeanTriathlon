/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section

open MeasureTheory

lemma ProbabilityMeasure.apply_compl {Z : Type*} [MeasurableSpace Z]
    (μ : ProbabilityMeasure Z) (A : Set Z) (A_mble : MeasurableSet A) :
    μ Aᶜ = 1 - μ A := by
  suffices μ.toMeasure Aᶜ = 1 - μ.toMeasure A by
    simp [ProbabilityMeasure.coeFn_def, this]
  simp [measure_compl A_mble]
