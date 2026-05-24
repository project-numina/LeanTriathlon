/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Connected.LocallyConnected
public import LiveLeanTriathlonSorry.Mathlib.Topology.Connected.Basic

@[expose] public section

open Set

theorem IsOpen.countable_connectedComponentsIn' {α : Type*}
    [TopologicalSpace α] [LocallyConnectedSpace α] [TopologicalSpace.SeparableSpace α]
    {s : Set α} (s_open : IsOpen s) :
    Countable (connectedComponentsIn s) := by
  apply Set.PairwiseDisjoint.countable_of_isOpen (α := α) (s := id)
  · exact connectedComponentsIn_pairwiseDisjoint
  · rintro _ ⟨_, _, rfl⟩
    exact s_open.connectedComponentIn
  · rintro _ ⟨x, hx_in, rfl⟩
    use x, mem_connectedComponentIn hx_in
