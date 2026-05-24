/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import LiveLeanTriathlonSorry.Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

lemma finrank_span_image' {ι 𝕜 M : Type*} [Fintype ι]  [RCLike 𝕜] [NormedAddCommGroup M]
    [InnerProductSpace 𝕜 M] (b : OrthonormalBasis ι 𝕜 M) (I : Finset ι) :
    Module.finrank 𝕜 (Submodule.span 𝕜 (b '' I)) = I.card :=
  finrank_span_image b.toBasis I
