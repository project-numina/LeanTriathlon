/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

@[to_additive]
lemma Finset.ite_prod {ι M : Type*} [CommMonoid M] {s1 s2 : Finset ι} (p : Prop) [Decidable p]
    (f : ι → M) : ∏ i ∈ if p then s1 else s2, f i = if p then ∏ i ∈ s1, f i else ∏ i ∈ s2, f i := by
  split_ifs <;> simp

lemma Finset.card_ite {ι : Type*} {s1 s2 : Finset ι} (p : Prop) [Decidable p] :
    (if p then s1 else s2).card = if p then s1.card else s2.card := by
  split_ifs <;> simp
