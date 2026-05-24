/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey and Numina team
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Basic

@[expose] public section

lemma Fintype.card_eq_finsetCard_of_inj {α β} [Fintype α] (f : α ↪ β) :
    Fintype.card α = (Finset.univ.map f).card := by
  classical
  rw [Fintype.card, Finset.card_map, Finset.card_univ]
