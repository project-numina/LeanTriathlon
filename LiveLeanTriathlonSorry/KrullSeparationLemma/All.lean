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

open Ideal

universe u

@[AMS 13]
theorem krull_separation {R : Type u} [CommRing R] {M : Submonoid R} {I : Ideal R}
    (h : M.carrier ∩ I.carrier = ∅) :
    ∃ P : Ideal R, IsPrime P ∧ M.carrier ∩ P.carrier = ∅ ∧ I ≤ P := sorry

end Main
