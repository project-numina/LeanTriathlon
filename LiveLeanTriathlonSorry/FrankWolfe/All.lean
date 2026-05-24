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

open Set

variable {d : ℕ}

noncomputable def frankWolfeSeq
    (lmo : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x₀ : EuclideanSpace ℝ (Fin d)) : ℕ → EuclideanSpace ℝ (Fin d)
  | 0 => x₀
  | k + 1 =>
    let xk := frankWolfeSeq lmo x₀ k
    xk + (2 / ((k : ℝ) + 2)) • (lmo xk - xk)

@[AMS 49]
theorem frank_wolfe_convergence_rate
    {D : Set (EuclideanSpace ℝ (Fin d))} {f : EuclideanSpace ℝ (Fin d) → ℝ} {L : NNReal}
    {lmo : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {x₀ x_star : EuclideanSpace ℝ (Fin d)}
    (hD_compact : IsCompact D)
    (hD_convex : Convex ℝ D)
    (hf_convex : ConvexOn ℝ D f)
    (hf_diff : Differentiable ℝ f)
    (hf_smooth : LipschitzOnWith L (fderiv ℝ f) D)
    (hx₀_mem : x₀ ∈ D)
    (hx_star_mem : x_star ∈ D)
    (hx_star_min : IsMinOn f D x_star)
    (hlmo_mem : ∀ x ∈ D, lmo x ∈ D)
    (hlmo_min : ∀ x ∈ D, IsMinOn (fun s => fderiv ℝ f x s) D (lmo x))
    : ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
        f (frankWolfeSeq lmo x₀ k) - f x_star ≤ C / ((k : ℝ) + 2) := by sorry

end Main
