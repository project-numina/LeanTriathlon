/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import LiveLeanTriathlonSorry.Mathlib.MeasureTheory.Pointwise
public import LiveLeanTriathlonSorry.Mathlib.MeasureTheory.InnerRegular
public import LiveLeanTriathlonSorry.Mathlib.MeasureTheory.IsEssBdd
public import LiveLeanTriathlonSorry.Util.Attributes

@[expose] public section

open ENNReal MeasureTheory Pointwise Real Set Filter MeasurableSet

abbrev PL_dim1_cond (t : ℝ) (f g h : EuclideanSpace ℝ (Fin 1) → ℝ) :=
  (x y : EuclideanSpace ℝ (Fin 1)) → (f x) ^ (1 - t) * (g y) ^ t ≤ h (x + y)

abbrev PL_dim1_conclusion (t : ℝ) (f g h : EuclideanSpace ℝ (Fin 1) → ℝ) :=
  (∫ x, f x) ^ (1 - t) * (∫ y, g y) ^ t ≤ (1 - t) ^ (1 - t) * t ^ t * (∫ x, h x)

@[AMS 28]
lemma prekopa_leindler_dim1
    {t : ℝ} (h0t : 0 < t) (ht1 : t < 1) {f g h : EuclideanSpace ℝ (Fin 1) → ℝ} (hf_nonneg : 0 ≤ f)
    (hf_integrable : Integrable f) (hg_nonneg : 0 ≤ g) (hg_integrable : Integrable g)
    (hh_nonneg : 0 ≤ h) (hh_integrable : Integrable h) (hfgh_pow_le : PL_dim1_cond t f g h) :
    PL_dim1_conclusion t f g h := by sorry
