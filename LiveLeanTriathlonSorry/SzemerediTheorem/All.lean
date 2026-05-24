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

open Nat Filter Set

noncomputable def upperDensity (A : Set ℕ) : ℝ :=
  limsup (fun (n : ℕ) ↦ (A ∩ Icc 0 n).ncard / (↑n : ℝ)) atTop

@[AMS 05]
theorem szemeredi {A : Set ℕ} (h : 0 < upperDensity A) (n : ℕ) :
  ∃ a b : ℕ, b > 0 ∧ {a + k * b | k < n} ⊆ A := sorry

end Main
