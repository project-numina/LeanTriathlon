/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.GDelta.MetrizableSpace
public import LiveLeanTriathlonSorry.Util.Attributes
@[expose] public section

section Background

open Set Topology

universe u

variable (k : ℕ) {V : Type u} (G : SimpleGraph V)

def ValidFiniteColorings (F : Finset V) : Set (V → Fin k) :=
  { f | ∀ u ∈ F, ∀ v ∈ F, G.Adj u v → f u ≠ f v }

end Background

section Main

open Set Topology Finset

universe u

variable (k : ℕ) {V : Type u} (G : SimpleGraph V)

@[AMS 05]
theorem SimpleGraph.colorable_of_finitely_colorable
    (hS : ∀ F, (ValidFiniteColorings k G F).Nonempty) :
    G.Colorable k := by sorry

end Main
