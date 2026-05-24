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

def degreeMultiset {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Multiset ℕ :=
  (Finset.univ : Finset V).val.map (fun v => G.degree v)

def degreeList {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    List ℕ :=
  (degreeMultiset G).sort (· ≥ ·)

@[AMS 05]
theorem ErdosGallaiTheorem (d : List ℕ) (hd : d.SortedGE) :
    (∃ V, ∃ fV : Fintype V, ∃ G : SimpleGraph V, ∃ dG : DecidableRel G.Adj, degreeList G = d) ↔
    Even d.sum ∧
    ∀ k ∈ Set.Ioc 0 d.length,
      (d.take k).sum ≤ k * (k - 1) + ((d.drop k).map fun x => min x k).sum := by sorry

end Main
