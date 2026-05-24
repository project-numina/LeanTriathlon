/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib
public import LiveLeanTriathlonSorry.Util.Attributes
@[expose] public section

section Main

universe u

open Filter Function Topology

def convergentSeries {α : Type u} [AddCommMonoid α] [TopologicalSpace α] (f : ℕ → α) : Prop :=
    ∃ l : α, Tendsto (fun n ↦ ∑ k ∈ Finset.range n, f k) atTop (𝓝 l)

@[AMS 40]
theorem riemann_summation_atbot {a : ℕ → ℝ}
    (h : convergentSeries a) (h' : ¬ convergentSeries (fun n ↦ |a n|)) :
    ∃ p : ℕ → ℕ, Bijective p ∧ Tendsto (fun n ↦ ∑ k ∈ Finset.range n, a (p k)) atTop atBot := sorry

end Main
