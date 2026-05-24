/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Data.ENat.Lattice
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import LiveLeanTriathlonSorry.Util.Attributes
public import LiveLeanTriathlonSorry.Mathlib.LinearAlgebra.Eigenspace.Basic
@[expose] public section

section Background

open Matrix

variable {n : ℕ}

def IsSubordinateMatrixNorm (norm : Matrix (Fin n) (Fin n) ℂ → ℝ) : Prop :=
  (∀ M₁ M₂ : Matrix (Fin n) (Fin n) ℂ, norm (M₁ * M₂) ≤ norm M₁ * norm M₂) ∧
  (∀ M : Matrix (Fin n) (Fin n) ℂ, ∀ γ : ℂ, Module.End.HasEigenvalue (toLin' M) γ →
    ‖γ‖ ≤ norm M) ∧
  (∀ M : Matrix (Fin n) (Fin n) ℂ, 0 ≤ norm M) ∧
  (∀ D : Matrix (Fin n) (Fin n) ℂ, D.IsDiag → norm D = ⨆ i : Fin n, ‖D i i‖) ∧
  (norm (1 : Matrix (Fin n) (Fin n) ℂ) = 1)

noncomputable def conditionNumber (norm : Matrix (Fin n) (Fin n) ℂ → ℝ)
    (V : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  norm V * norm V⁻¹

end Background

section Main

open Matrix BigOperators

variable {n : ℕ}

@[AMS 47]
theorem bauer_fike
    (A : Matrix (Fin n) (Fin n) ℂ) (V Λ δA : Matrix (Fin n) (Fin n) ℂ)
    (hV : IsUnit (V.det)) (hΛ : Λ.IsDiag) (hA : A = V * Λ * V⁻¹)
    (norm : Matrix (Fin n) (Fin n) ℂ → ℝ)
    (hnorm : IsSubordinateMatrixNorm norm)
    (μ : ℂ) (hμ : Module.End.HasEigenvalue (toLin' (A + δA)) μ) :
    ∃ i : Fin n, ‖Λ i i - μ‖ ≤ conditionNumber norm V * norm δA := by sorry

end Main
