/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Mathlib.Logic.IsEmpty.Defs
public import Mathlib.Logic.Nonempty
public import Mathlib.Tactic.Lemma

@[expose] public section

lemma Function.surjective_of_isEmpty {α β : Type*} [IsEmpty β] (f : α → β) :
    Function.Surjective f := by
  intro y
  exact IsEmpty.elim inferInstance y

lemma Function.not_surjective_of_isEmpty_Nonempty {α β : Type*} [IsEmpty α] [Nonempty β] (f : α → β) :
    ¬Function.Surjective f := by
  intro h_surj
  obtain ⟨y, _⟩ := h_surj (Classical.arbitrary β)
  exact IsEmpty.elim inferInstance y
