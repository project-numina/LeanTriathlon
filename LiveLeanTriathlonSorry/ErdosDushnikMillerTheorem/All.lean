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

open Cardinal in

@[AMS 03]
theorem erdos_dushnik_miller
    {V : Type*} [Infinite V] (G : SimpleGraph V) :
    (∃ s : Set V, G.IsClique s ∧ #s = #V) ∨
    (∃ s : Set V, G.IsIndepSet s ∧ ℵ₀ ≤ #s) := by sorry

end Main
