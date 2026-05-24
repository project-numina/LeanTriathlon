/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

lemma finrank_span_image {ι R M : Type*} [Nontrivial R] [Semiring R] [StrongRankCondition R]
    [AddCommMonoid M] [Module R M] (b : Module.Basis ι R M) (I : Finset ι) :
    Module.finrank R (Submodule.span R (b '' I)) = I.card := by
  classical
  rw [@finrank_span_set_eq_card _ _ _ _ _ _ _ (Fintype.ofFinite _)
    (LinearIndepOn.mono (linearIndepOn_id_range_iff b.injective |>.2 b.linearIndependent)
    (by grind : _ ⊆ Set.range b)), Set.toFinset_image, I.toFinset_coe, I.card_image_of_injective]
  exact b.injective
