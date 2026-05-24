/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä and Numina team
-/
module

public import Mathlib.Probability.Process.Adapted

@[expose] public section

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma Filtration.adapted_natural_nat {α : Type*} {β : Type*}
    [MeasurableSpace α] [TopologicalSpace α] [TopologicalSpace.MetrizableSpace α]
    [SecondCountableTopology α] [BorelSpace α]
    [MeasurableSpace β] [TopologicalSpace β] [TopologicalSpace.MetrizableSpace β]
    [SecondCountableTopology β] [OpensMeasurableSpace β]
    {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → α} (X_mble : ∀ n, Measurable (X n))
    (fs : Π (n : ℕ), (Fin n → α) → β) (fs_mble : ∀ n, Measurable (fs n)) :
    StronglyAdapted (m := ‹MeasurableSpace Ω›) (Filtration.natural X (by measurability))
      (fun (n : ℕ) ω ↦ (fs n) (fun (i : Fin n) ↦ X i ω)) := by
  intro n
  apply Measurable.stronglyMeasurable
  apply (fs_mble n).comp
  apply (@measurable_pi_iff Ω (Fin n) (fun _ ↦ α) (Filtration.natural X (by measurability) n) _).mpr
  intro i
  have key := (Filtration.stronglyAdapted_natural (u := X) (by measurability) i).measurable
  apply key.mono _ le_rfl
  exact (Filtration.natural X (by measurability)).mono Fin.is_le'

lemma Filtration.adapted_natural_nat' {α : Type*} {β : Type*}
    [MeasurableSpace α] [TopologicalSpace α] [TopologicalSpace.MetrizableSpace α]
    [SecondCountableTopology α] [BorelSpace α]
    [MeasurableSpace β] [TopologicalSpace β] [TopologicalSpace.MetrizableSpace β]
    [SecondCountableTopology β] [OpensMeasurableSpace β]
    {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → α} (X_mble : ∀ n, Measurable (X n))
    (fs : Π (n : ℕ), (Finset.range n → α) → β) (fs_mble : ∀ n, Measurable (fs n)) :
    StronglyAdapted (m := ‹MeasurableSpace Ω›) (Filtration.natural X (by measurability))
      (fun (n : ℕ) ω ↦ (fs n) (fun (i : Finset.range n) ↦ X i ω)) := by
  intro n
  apply Measurable.stronglyMeasurable
  apply (fs_mble n).comp
  apply (@measurable_pi_iff Ω (Finset.range n) (fun _ ↦ α) (Filtration.natural X (by measurability) n) _).mpr
  intro i
  have key := (Filtration.stronglyAdapted_natural (u := X) (by measurability) i).measurable
  apply key.mono _ le_rfl
  apply (Filtration.natural X (by measurability)).mono
  exact (Finset.mem_range.mp i.prop).le
