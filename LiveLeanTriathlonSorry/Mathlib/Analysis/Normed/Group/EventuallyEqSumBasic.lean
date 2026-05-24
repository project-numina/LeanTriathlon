/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä and Numina team
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Order.Filter.Cofinite

@[expose] public section

open Filter

lemma Filter.EventuallyEq.eventually_sum_eq_sum_add_finsum_sub_of_cofinite
    {ι : Type*} [DecidableEq ι] {R : Type*} [AddCommGroup R]
    {a b : ι → R} (hab : a =ᶠ[cofinite] b) :
    ∀ᶠ s in (atTop : Filter (Finset ι)),
      ∑ i ∈ s, a i = ∑ i ∈ s, b i + ∑ᶠ i, (a i - b i) := by
  have obs : ∃ (t : Finset ι), ∀ i ∉ t, a i = b i := by
    have hab' : {i | a i ≠ b i}.Finite := by
      convert mem_cofinite.mp hab using 1
    refine ⟨hab'.toFinset, by simp⟩
  obtain ⟨t, ht⟩ := obs
  filter_upwards [show Set.Ici t ∈ atTop from mem_atTop_sets.mpr ⟨t, by simp⟩] with s hs
  simp only [Set.mem_Ici, Finset.le_eq_subset] at hs
  have decomp : s = t ∪ (s \ t) := by simp [hs]
  have decomp_disj : Disjoint t (s \ t) := Finset.disjoint_sdiff
  suffices ∑ i ∈ t ∪ (s \ t), a i = ∑ i ∈ t ∪ (s \ t), b i + ∑ᶠ (i : ι), (a i - b i) by
    convert this
  simp_rw [Finset.sum_union decomp_disj]
  have := Finset.sum_congr (s₁ := s \ t) (s₂ := s \ t) (f := a) (g := b) rfl ?_
  · simp only [this, add_comm (∑ i ∈ t, _), add_assoc, add_right_inj]
    rw [← sub_eq_iff_eq_add, ← Finset.sum_sub_distrib]
    rw [finsum_eq_sum_of_support_subset]
    intro i hi
    by_contra con
    simp [ht _ con] at hi
  · intro i hi
    exact ht _ (decomp_disj.symm.notMem_of_mem_left_finset hi)

lemma Filter.EventuallyEq.eventually_sum_range_eq_sum_range_add_finsum_sub_of_cofinite
    {R : Type*} [AddCommGroup R] {a b : ℕ → R} (hab : a =ᶠ[cofinite] b) :
    ∀ᶠ N in (atTop : Filter ℕ),
      ∑ i ∈ Finset.range N, a i = ∑ i ∈ Finset.range N, b i + ∑ᶠ i, (a i - b i) := by
  obtain ⟨s, hs⟩ :=
    mem_atTop_sets.mp hab.eventually_sum_eq_sum_add_finsum_sub_of_cofinite
  simp only [eventually_atTop, ge_iff_le]
  let N := (s ∪ {0}).max' (by aesop) + 1
  use N
  intro n hn
  specialize hs (Finset.range n) ?_
  · apply le_trans _ (Finset.range_mono hn)
    intro i hi
    simp only [Finset.union_singleton, Finset.mem_range, N]
    rw [Order.lt_add_one_iff]
    exact Finset.le_max' _ _ (Finset.mem_insert_of_mem hi)
  · simpa using hs
