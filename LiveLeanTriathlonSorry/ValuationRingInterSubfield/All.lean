/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Tactic.NormNum
public import LiveLeanTriathlonSorry.Util.Attributes
@[expose] public section

section Main

open Subring Subfield

variable {L : Type*} [Field L]

@[AMS 13]
theorem ValuationRing.inter_subfield
    (B : Subring L) [ValuationRing B] (K : Subfield L) :
    ValuationRing ↥(K.toSubring ⊓ B) := by sorry

end Main
