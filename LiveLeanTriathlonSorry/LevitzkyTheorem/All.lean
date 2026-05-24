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

def Ideal.IsNil {R : Type*} [Ring R] (I : Ideal R) : Prop :=
  ∀ (x : R), x ∈ I → IsNilpotent x

@[AMS 17]
theorem levitzky_theorem {R : Type*} [Ring R]
    [IsNoetherianRing (MulOpposite R)]
    (I : Ideal R) (hnil : I.IsNil) :
    IsNilpotent I := by sorry

end Main
