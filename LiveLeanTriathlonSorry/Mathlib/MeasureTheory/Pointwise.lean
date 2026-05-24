/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Mathlib.MeasureTheory.Group.Measure

@[expose] public section

open MeasureTheory Pointwise Set

lemma volume_le_volume_add_right {α : Type*} [MeasureSpace α] [AddGroup α] [MeasurableAdd α]
    {μ : Measure α} [μ.IsAddRightInvariant] {A B : Set α} (hB : B.Nonempty) :
  μ A ≤ μ (A + B) := (by simp : μ A = μ (A + {hB.choose})) ▸
  (measure_mono <| add_subset_add_left <| singleton_subset_iff.2 hB.choose_spec)

lemma volume_le_volume_add_left {α : Type*} [MeasureSpace α] [AddGroup α] [MeasurableAdd α]
    {μ : Measure α} [μ.IsAddLeftInvariant] {A B : Set α} (hB : B.Nonempty) :
  μ A ≤ μ (B + A) := (by simp : μ A = μ ({hB.choose} + A)) ▸
  (measure_mono <| add_subset_add_right <| singleton_subset_iff.2 hB.choose_spec)

lemma Set.mem_vAdd_le_Add {α} [Add α] {A B : Set α} {x : α} (hx : x ∈ A) : x +ᵥ B ⊆ A + B :=
  singleton_vadd (a := x) (t := B).symm ▸ add_subset_add_right (by grind)
