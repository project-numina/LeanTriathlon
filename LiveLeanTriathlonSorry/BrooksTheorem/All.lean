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

open Finset

@[AMS 05]
theorem brooks_theorem {V : Type} (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (h_connected : G.Connected) :
    (G.chromaticNumber ≤ G.maxDegree) ∨
    (∃ n : ℕ, Nonempty (G ≃g SimpleGraph.completeGraph (Fin n))) ∨
    (∃ n : ℕ, Nonempty (G ≃g SimpleGraph.cycleGraph (2 * n + 3))) := by sorry

end Main
