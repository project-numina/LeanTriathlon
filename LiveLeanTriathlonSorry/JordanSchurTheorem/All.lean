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

open Function Set Matrix Group

variable (n : ℕ)

structure Subgroup.Abelian (G : Type*) [Group G] (H : Subgroup G) : Prop where
  mul_comm : ∀ᵉ (a ∈ H) (b ∈ H), a * b = b * a

@[AMS 20]
theorem jordan_schur : ∃ f : ℕ → ℝ, ∀ n : ℕ, ∀ G : Subgroup (GeneralLinearGroup (Fin n) ℂ),
    Finite G → ∃ H : Subgroup G, H.Normal ∧ H.Abelian ∧ H.index ≤ f n := by sorry

end Main
