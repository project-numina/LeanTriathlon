/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Mathlib.Data.Multiset.Fintype

@[expose] public section

@[to_additive]
lemma Multiset.prod_map_eq_prod_toType {α β : Type*} [DecidableEq α] [CommMonoid β]
    (s : Multiset α) (f : α → β) :
    (s.map f).prod = ∏ a : s.ToType, f a := by
  congr 1
  simp
