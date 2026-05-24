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

open SimpleGraph SimpleGraph.Subgraph

open scoped symmDiff

variable {V : Type*} {G G' : SimpleGraph V}

def SimpleGraph.Subgraph.IsAugmentingPath (M : G.Subgraph) {u v : V} (p : G.Walk u v) : Prop :=
  p.IsPath ∧
  u ∉ M.support ∧
  v ∉ M.support ∧
  u ≠ v ∧
  p.toSubgraph.spanningCoe.IsAlternating M.spanningCoe

private noncomputable def augmentingSymmDiff (M : G.Subgraph) {u v : V} (p : G.Walk u v) :
    G.Subgraph where
  verts := {w | ∃ x, (M.spanningCoe ∆ p.toSubgraph.spanningCoe).Adj w x}
  Adj := (M.spanningCoe ∆ p.toSubgraph.spanningCoe).Adj
  adj_sub h :=
    symmDiff_le_sup.trans (sup_le (Subgraph.spanningCoe_le M) (p.toSubgraph.spanningCoe_le)) h
  edge_vert h := ⟨_, h⟩
  symm := (M.spanningCoe ∆ p.toSubgraph.spanningCoe).symm

@[AMS 05]
theorem SimpleGraph.Subgraph.IsMatching.berge
    [Fintype V] [DecidableEq V] {M : G.Subgraph} (hM : M.IsMatching) :
    (∀ M' : G.Subgraph, M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard) ↔
    ∀ {u v : V} (p : G.Walk u v), ¬M.IsAugmentingPath p := by sorry

end Main
