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

def SimpleGraph.IsRegularOfDegree'.{u} {V : Type u} (G : SimpleGraph V)
    (d : ℕ) : Prop :=
  ∃ _ : G.LocallyFinite, G.IsRegularOfDegree d

@[AMS 5]
theorem two_factor_theorem  {V : Type} (G : SimpleGraph V) {k : ℕ}
    (h : G.IsRegularOfDegree' (2 * k)) :
  ∃ (factors : Fin k → SimpleGraph V),
    (∀ i, factors i ≤ G) ∧
    (∀ i, (factors i).IsRegularOfDegree' 2) ∧
    (∀ i j, i ≠ j → Disjoint (factors i).edgeSet (factors j).edgeSet) ∧
    (⋃ i, (factors i).edgeSet) = G.edgeSet := sorry

end Main
