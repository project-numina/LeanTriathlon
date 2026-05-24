/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä and Numina team
-/

module
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.Probability.BorelCantelli
public import LiveLeanTriathlonSorry.Mathlib.Analysis.Normed.Group.EventuallyEqSum
public import LiveLeanTriathlonSorry.Mathlib.Probability.Moments.VarianceALittleMore
public import LiveLeanTriathlonSorry.Util.Attributes
public import LiveLeanTriathlonSorry.KolmogorovThreeSeriesSufficient.All
public import LiveLeanTriathlonSorry.Mathlib.Probability.Martingale.Basic
@[expose] public section

section Main

open MeasureTheory ProbabilityTheory Filter Topology

open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

@[AMS 40]
theorem kolmogorov_three_series_necessity
    (X : ℕ → Ω → ℝ) (X_mble : ∀ n, Measurable (X n)) (X_indep : iIndepFun X P)
    (X_sum_ae : ∀ᵐ ω ∂P, ∃ s, Tendsto (fun N ↦ ∑ n ∈ Finset.range N, X n ω) atTop (𝓝 s))
    {b : ℝ} (b_pos : 0 < b) :
    (∑' n, P {ω | b < |X n ω|} ≠ ∞) ∧
      (∃ s,
      Tendsto (fun N ↦ ∑ n ∈ Finset.range N, ∫ ω, ((Set.indicator {ω | |X n ω| ≤ b} (X n)) ω) ∂P)
        atTop (𝓝 s)) ∧
      (∑' n, evariance (Set.indicator {ω | |X n ω| ≤ b} (X n)) P ≠ ∞) := by sorry

end Main
