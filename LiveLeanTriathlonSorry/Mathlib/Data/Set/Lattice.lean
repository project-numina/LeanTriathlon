/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Mathlib.Order.SetNotation
public import Mathlib.Data.Set.Basic

@[expose] public section

theorem inter_sUnion {α} {A : Set α} (I : Set (Set α)) :
    A ∩ ⋃₀ I = ⋃ i ∈ I, A ∩ i := by
  ext x
  simp
