/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä and Numina team
-/
module

public import LiveLeanTriathlonSorry.Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Probability.Moments.Variance

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma evariance_add_const {Z : Ω → ℝ} (Z_mble : AEStronglyMeasurable Z P) (c : ℝ) :
    eVar[Z + fun _ ↦ c; P] = eVar[Z; P] := by
  by_cases Z_mem_L2 : MemLp Z 2 P
  · have Z_add_c_mem_L2 : MemLp (Z + fun _ ↦ c) 2 P := by simp [Z_mem_L2]
    suffices Var[Z + fun _ ↦ c; P] = Var[Z; P] by
      simp [variance] at this
      obtain h1 | h2 | h2 := ENNReal.toReal_eq_toReal_iff _ _ |>.1 this
      · assumption
      · exact False.elim <| Z_mem_L2.evariance_ne_top h2.2
      · exact False.elim <| Z_add_c_mem_L2.evariance_ne_top h2.1
    exact variance_add_const (X := Z) Z_mble c
  · have Z_add_c_not_mem_L2 : ¬ MemLp (Z + fun _ ↦ c) 2 P := by simp [Z_mem_L2]
    simp [(evariance_eq_top_iff Z_mble).mpr Z_mem_L2,
          (evariance_eq_top_iff (by measurability)).mpr Z_add_c_not_mem_L2]

lemma evariance_sub_const {Z : Ω → ℝ} (Z_mble : AEStronglyMeasurable Z P) (c : ℝ) :
    eVar[Z - fun _ ↦ c; P] = eVar[Z; P] := by
  simp_rw [sub_eq_add_neg]
  exact evariance_add_const Z_mble (-c)
