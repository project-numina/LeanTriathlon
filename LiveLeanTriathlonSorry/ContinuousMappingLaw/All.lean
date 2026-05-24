/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä and Numina team
-/

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import LiveLeanTriathlonSorry.Util.Attributes
public import LiveLeanTriathlonSorry.Mathlib.MeasureTheory.Measure.ProbabilityMeasure
@[expose] public section

section Main

open MeasureTheory ProbabilityTheory Filter Topology ENNReal NNReal

open scoped ENNReal

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

variable [MeasurableSpace X] [OpensMeasurableSpace X] [MeasurableSpace Y] [OpensMeasurableSpace Y]

variable {Ps : ℕ → ProbabilityMeasure X} {P : ProbabilityMeasure X}

variable {X₀ : Set X} {g : X → Y}

@[AMS 60]
theorem ProbabilityMeasure.tendsto_map_of_forall_continuousAt
    (g_cont : ∀ x ∈ X₀, ContinuousAt g x) (g_mble : Measurable g)
    (P_supp : ∀ᵐ x ∂(P.toMeasure), x ∈ X₀) (Ps_lim : Tendsto Ps atTop (𝓝 P)) :
    Tendsto (fun n ↦ (Ps n).map g_mble.aemeasurable) atTop (𝓝 (P.map g_mble.aemeasurable)) := by sorry

end Main
