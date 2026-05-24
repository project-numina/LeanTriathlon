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

open Complex Set Metric Filter Topology

def IsolatedUnremovableSingularity (f : ℂ → ℂ) (c : ℂ) : Prop :=
  ∃ s ∈ 𝓝 c, DifferentiableOn ℂ f (s \ {c})
    ∧ (¬∃ g : ℂ → ℂ, EqOn f g (s \ {c}) ∧ DifferentiableAt ℂ g c)

def EssentialSingularity (f : ℂ → ℂ) (c : ℂ) : Prop :=
  IsolatedUnremovableSingularity f c ∧ ¬∀ M, ∃ ε > 0, ∀ z, z ≠ c → dist z c < ε → M ≤ ‖f z‖

@[AMS 30]
theorem casorati_weierstrass (f : ℂ → ℂ) {s : Set ℂ} {c : ℂ}
    (hess : EssentialSingularity f c)
    (hc : s ∈ 𝓝 c) (hd : DifferentiableOn ℂ f (s \ {c})) :
    Dense (f '' s) := by sorry

end Main
