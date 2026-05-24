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

@[AMS 30]
theorem mergelyan {K : Set ℂ} (K_compact : IsCompact K) (K_conn : IsConnected Kᶜ)
    {f : ℂ → ℂ} (f_cont : ContinuousOn f K) (f_diff : DifferentiableOn ℂ f (interior K)) :
    ∀ ε > 0, ∃ p : Polynomial ℂ, ∀ x ∈ K, ‖f x - p.eval x‖ₑ < ε := by sorry

end Main
