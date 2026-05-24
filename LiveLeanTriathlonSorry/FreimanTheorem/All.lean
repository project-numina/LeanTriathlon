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

open Nat Finset Set Pointwise

structure GFLP where
  dim : Nat
  x0 : ℤ
  x : Fin dim → ℤ
  L : Fin dim → ℕ

def setOfGFLP (A : GFLP) : Set ℤ :=
  {e | ∃ f : Fin A.dim → ℕ, (∀ i : Fin A.dim, f i < A.L i)
    ∧ e = A.x0 + ∑ i : Fin A.dim, f i * A.x i}
noncomputable

def QuotSum (A : Finset ℤ) : ℝ :=
  (A + A).card / (A.card : ℝ)

@[AMS 11]
theorem Freiman (K : ℝ) : ∃ dim size : ℕ,
    ∀ A : Finset ℤ, QuotSum A ≤ K →
      ∃ L : GFLP,
        ↑A ⊆ setOfGFLP L
        ∧ L.dim ≤ dim
        ∧ (setOfGFLP L).ncard ≤ size * A.card := by sorry

end Main
