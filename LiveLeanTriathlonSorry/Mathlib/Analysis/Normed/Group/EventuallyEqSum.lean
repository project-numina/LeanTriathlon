/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä and Numina team
-/
module

public import LiveLeanTriathlonSorry.Mathlib.Analysis.Normed.Group.EventuallyEqSumBasic
public import Mathlib.Analysis.Normed.Group.Uniform

@[expose] public section

open Filter Topology

lemma Filter.EventuallyEq.tendsto_sum_range_add_finsum_of_cofinite
    {R : Type*} [NormedAddCommGroup R] {a b : ℕ → R} (hab : a =ᶠ[cofinite] b)
    {s : R} (sum_a : Tendsto (fun N ↦ ∑ i ∈ Finset.range N, a i) atTop (𝓝 s)) :
    Tendsto (fun N ↦ ∑ i ∈ Finset.range N, b i) atTop (𝓝 (s + ∑ᶠ i, (b i - a i))) := by
  have obs := hab.eventually_sum_range_eq_sum_range_add_finsum_sub_of_cofinite
  have key := Tendsto.congr' obs (l₂ := 𝓝 s) sum_a
  have key' := key.sub (tendsto_const_nhds (x := ∑ᶠ (i : ℕ), (a i - b i)))
  simp only [add_sub_cancel_right] at key'
  convert key' using 2
  rw [sub_eq_add_neg s, ← finsum_neg_distrib]
  congr with n
  simp

lemma Filter.EventuallyEq.exists_tendsto_sum_range_iff_of_cofinite
    {R : Type*} [NormedAddCommGroup R] {a b : ℕ → R} (hab : a =ᶠ[cofinite] b) :
    (∃ s, Tendsto (fun N ↦ ∑ i ∈ Finset.range N, a i) atTop (𝓝 s)) ↔
      (∃ s, Tendsto (fun N ↦ ∑ i ∈ Finset.range N, b i) atTop (𝓝 s)) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨s, hs⟩ := h
    refine ⟨_, tendsto_sum_range_add_finsum_of_cofinite hab hs⟩
  · obtain ⟨s, hs⟩ := h
    refine ⟨_, tendsto_sum_range_add_finsum_of_cofinite hab.symm hs⟩
