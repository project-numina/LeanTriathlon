/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Tactic.NormNum.GCD

@[expose] public section

lemma Matrix.IsSymm.mulVec_dotProduct_comm {n R : Type*} [Fintype n] [CommRing R]
    {A : Matrix n n R} (hA : A.IsSymm) (x y : n → R) :
    (A.mulVec x) ⬝ᵥ y = x ⬝ᵥ (A.mulVec y) := by
  classical
  rw [dotProduct_mulVec, ← mulVec_transpose, hA.eq]
