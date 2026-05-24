/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Positivity

@[expose] public section

open ENNReal MeasureTheory Pointwise Real Set Filter MeasurableSet

open scoped Classical in
lemma MeasurableSet.exists_isCompact_Nonempty_diff_lt
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [TopologicalSpace α]
    [OpensMeasurableSpace α] [T2Space α] [μ.InnerRegularCompactLTTop]
    {A : Set α} (hA : A.Nonempty) (mA : MeasurableSet A) (h'A : μ A ≠ ⊤)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) : ∃ S ⊆ A, S.Nonempty ∧ IsCompact S ∧ μ (A \ S) < ε :=
  (mA.exists_isCompact_diff_lt h'A hε).casesOn fun S ⟨hS1, hS2, hS3⟩ ↦ if hS4 : S.Nonempty then
  ⟨S, hS1, hS4, hS2, hS3⟩ else ⟨{hA.choose}, singleton_subset_iff.2 hA.choose_spec,
  singleton_nonempty hA.choose, isCompact_singleton, lt_of_le_of_lt (measure_mono <| diff_subset)
  <| diff_empty (s := A) ▸ not_nonempty_iff_eq_empty.1 hS4 ▸ hS3⟩
