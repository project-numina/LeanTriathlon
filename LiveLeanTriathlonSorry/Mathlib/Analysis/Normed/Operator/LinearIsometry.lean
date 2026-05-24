/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.LinearAlgebra.Dimension.Finrank

@[expose] public section

lemma LinearIsometryEquiv.finrank_map_eq {R E1 E2 : Type*} [Semiring R]
    [SeminormedAddCommGroup E1] [SeminormedAddCommGroup E2]
    [Module R E1] [Module R E2] (e : E1 ≃ₗᵢ[R] E2) (S : Submodule R E1) :
    Module.finrank R (S.map (e.toLinearMap)) = Module.finrank R S :=
  e.toLinearEquiv.finrank_map_eq S
