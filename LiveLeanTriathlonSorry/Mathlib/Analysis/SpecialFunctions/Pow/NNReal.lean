/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä and Numina team
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

@[expose] public section

open scoped ENNReal NNReal

lemma ENNReal.pow_nat_pow_inv (x : ℝ≥0∞) {n : ℕ} (hn : n ≠ 0) :
    (x ^ n) ^ (n⁻¹ : ℝ) = x := by
  convert (ENNReal.rpow_mul x n n⁻¹).symm <;> simp [hn]

lemma ENNReal.pow_inv_pow_nat (x : ℝ≥0∞) {n : ℕ} (hn : n ≠ 0) :
    (x ^ (n⁻¹ : ℝ)) ^ n = x := by
  convert (ENNReal.rpow_mul x n⁻¹ n).symm <;> simp [hn]

@[simp] lemma ENNReal.pow_two_pow_half (x : ℝ≥0∞) : (x ^ 2) ^ (2⁻¹ : ℝ) = x :=
  ENNReal.pow_nat_pow_inv x (by simp)

@[simp] lemma ENNReal.pow_half_pow_two (x : ℝ≥0∞) : (x ^ (2⁻¹ : ℝ)) ^ 2 = x :=
  ENNReal.pow_inv_pow_nat x (by simp)

lemma ENNReal.injective_pow_nat {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (fun (x : ℝ≥0∞) ↦ x ^ n) := by
  intro x y hxy
  by_cases hx : x = ∞
  · simp only [hx, top_pow hn] at *
    exact (eq_top_of_pow n hxy.symm).symm
  · have obs : x.toNNReal = y.toNNReal := by
      simp only at hxy
      apply (pow_left_inj₀ (by positivity) (by positivity) hn).mp
      simpa using congr_arg ENNReal.toNNReal hxy
    exact (toNNReal_eq_toNNReal_iff' hx (by aesop)).mp obs

lemma ENNReal.injective_sq : Function.Injective (fun (x : ℝ≥0∞) ↦ x ^ 2) :=
  injective_pow_nat two_ne_zero
