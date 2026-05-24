/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import LiveLeanTriathlonSorry.Mathlib.Order.Interval.Set.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

open Real Set Pointwise MeasureTheory

theorem volume_union_add_self_ge_of_Ioo_nonneg {a b : ℝ}
    (t : ℝ) (ht_nonneg : 0 ≤ t) (ht : t < b - a) :
    ENNReal.ofReal (b - a + t) ≤ MeasureTheory.volume ((Set.Ioo a b) ∪ ({t} + (Set.Ioo a b))) := by
  simp
  rw [Ioo_union_Ioo_translate_nonneg ht_nonneg ht]
  rw [Real.volume_Ioo]
  apply ENNReal.ofReal_le_ofReal
  linarith

lemma volume_union_add_self_ge_of_Ioo_nonpos {a b : ℝ}
    (t : ℝ) (ht_nonpos : t < 0) (ht : -t < b - a) :
    ENNReal.ofReal (b - a - t) ≤ MeasureTheory.volume ((Set.Ioo a b) ∪ ({t} + (Set.Ioo a b))) := by

  · simp
    rw [Ioo_union_Ioo_translate_nonpos ht_nonpos ht]
    rw [Real.volume_Ioo]
    apply ENNReal.ofReal_le_ofReal
    linarith

lemma volume_union_add_self_ge_of_Ioo' {a b : ℝ}
    (t : ℝ) (ht : |t| < b - a) :
    ENNReal.ofReal (b - a + |t|) ≤ MeasureTheory.volume ((Set.Ioo a b) ∪ ({t} + (Set.Ioo a b))) := by
  by_cases h : 0 ≤ t
  · rw [abs_of_nonneg h]
    have ht_bound : t < b - a := by rwa [abs_of_nonneg h] at ht
    exact volume_union_add_self_ge_of_Ioo_nonneg t h ht_bound
  · push Not at h
    rw [abs_of_neg h]
    have h_bound_neg_t : -t < b - a := by rwa [← abs_of_neg h]
    exact volume_union_add_self_ge_of_Ioo_nonpos t h h_bound_neg_t

section Subset

theorem volume_union_add_self_ge_of_Ioo_subset_nonneg {J : Set ℝ} {a b : ℝ} (J_ge : Set.Ioo a b ⊆ J)
    (t : ℝ) (ht_nonneg : 0 ≤ t) (ht : t < b - a) :
    ENNReal.ofReal (b - a + t) ≤ MeasureTheory.volume (J ∪ ({t} + J)) := by
  trans volume ((Set.Ioo a b) ∪ ({t} + (Set.Ioo a b)))
  · exact volume_union_add_self_ge_of_Ioo_nonneg t ht_nonneg ht
  · apply measure_mono
    exact union_subset_union J_ge (add_subset_add (subset_refl _) J_ge)

lemma volume_union_add_self_ge_of_Ioo_subset_nonpos {J : Set ℝ} {a b : ℝ} (J_ge : Set.Ioo a b ⊆ J)
    (t : ℝ) (ht_nonpos : t < 0) (ht : -t < b - a) :
    ENNReal.ofReal (b - a - t) ≤ MeasureTheory.volume (J ∪ ({t} + J)) := by
  trans volume ((Set.Ioo a b) ∪ ({t} + (Set.Ioo a b)))
  · exact volume_union_add_self_ge_of_Ioo_nonpos t ht_nonpos ht
  · apply measure_mono
    exact union_subset_union J_ge (add_subset_add (subset_refl _) J_ge)

lemma volume_union_add_self_ge_of_Ioo_subset {J : Set ℝ} {a b : ℝ} (J_ge : Set.Ioo a b ⊆ J)
    (t : ℝ) (ht : |t| < b - a) :
    ENNReal.ofReal (b - a + |t|) ≤ MeasureTheory.volume (J ∪ ({t} + J)) := by
  by_cases h : 0 ≤ t
  · rw [abs_of_nonneg h]
    have ht_bound : t < b - a := by rwa [abs_of_nonneg h] at ht
    exact volume_union_add_self_ge_of_Ioo_subset_nonneg J_ge t h ht_bound
  · push Not at h
    rw [abs_of_neg h]
    have h_bound_neg_t : -t < b - a := by rwa [← abs_of_neg h]
    exact volume_union_add_self_ge_of_Ioo_subset_nonpos J_ge t h h_bound_neg_t

end Subset
