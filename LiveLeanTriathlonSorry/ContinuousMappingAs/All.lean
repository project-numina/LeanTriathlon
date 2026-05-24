/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import LiveLeanTriathlonSorry.Util.Attributes
@[expose] public section

section Main

open MeasureTheory Filter Topology

open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {X₀ : Set X}

variable {g : X → Y}

@[AMS 60]
theorem ae_tendsto_comp_of_ae_tendsto_of_forall_continuousAt {ι : Type*} {F : Filter ι}
    {rvs : ι → Ω → X} {rv : Ω → X} (g_cont : ∀ x ∈ X₀, ContinuousAt g x)
    (rv_supp : ∀ᵐ ω ∂P, rv ω ∈ X₀) (rvs_lim_as : ∀ᵐ ω ∂P, Tendsto (rvs · ω) F (𝓝 (rv ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun i ↦ g (rvs i ω)) F (𝓝 (g (rv ω))) := by sorry

end Main
