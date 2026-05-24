/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import LiveLeanTriathlonSorry.Util.Attributes
@[expose] public section

section Background

variable (D : Type*) [DivisionRing D]

section mathlib

variable {K : Type*} [DivisionRing K]

variable (K) in

def Subfield.center  : Subfield K where
  __ := Subring.center K
  inv_mem' x hx := by
    classical
    change _ ∈ Subring.center K at hx ⊢
    simp [Subring.mem_center_iff] at hx ⊢
    refine fun y ↦ if hx' : x = 0 then by simp [hx'] else ?_
    simp [mul_inv_eq_iff_eq_mul₀ hx', hx, ← mul_assoc, mul_inv_cancel₀ hx']

end mathlib

end Background

section Main

@[AMS 13]
theorem cartan_brauer_hua {D : Type*} [DivisionRing D] (K : Subfield D)
    (hK1 : ∀ x : D, x ≠ 0 → ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hK2 : K ≠ ⊤) :
    K ≤ Subfield.center D := by sorry

end Main
