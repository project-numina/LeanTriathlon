/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey and Numina team
-/
module

public import Mathlib.Logic.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Finset.Defs

@[expose] public section

universe u

variable {P : Type u}

namespace Classical

lemma choose_mem_of_finset_subset {S : Set P} {hS : S.Nonempty} (S' : Finset P)
    (hSS' : S ⊆ SetLike.coe S') : (hS.choose : P) ∈ S' := by
  convert hSS' hS.choose_spec

lemma choose_spec_of {α : Sort u} {p q : α → Prop} (h : ∃ (x : α), p x)
    (hpq : ∀ x, p x → q x) :
    q (choose h) := hpq _ (choose_spec h)

lemma choose_spec_iff {α : Sort u} {p q : α → Prop} (h : ∃ (x : α), p x)
    (hpq : ∀ x, p x ↔ q x) :
    q (choose h) :=
  (hpq _).mp (choose_spec h)

end Classical
