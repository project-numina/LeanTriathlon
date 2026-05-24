/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Mathlib.Analysis.Complex.Norm

@[expose] public section

open ComplexConjugate

theorem Complex.norm_sq_div_eq_conj {z : ℂ} :
    ‖z‖ ^ 2 / z = conj z := by
  by_cases h : z = 0
  · simp_all
  field_simp [h, <-Complex.normSq_eq_conj_mul_self]
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem Complex.inv_eq_conj_div_norm_sq {z : ℂ} :
    z⁻¹ = conj z / ‖z‖ ^ 2 := by
  by_cases h : (‖z‖ : ℂ) ^ 2 = 0
  · simp_all
  have : z ≠ 0 := by
    simp at h
    exact fun hz ↦ by simp [hz] at h
  field_simp
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, this]
