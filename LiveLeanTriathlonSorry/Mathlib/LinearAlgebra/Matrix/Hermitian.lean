/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import LiveLeanTriathlonSorry.Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Hermitian

@[expose] public section

lemma Matrix.IsHermitian.toSymm_of_trivial {n R : Type*} [Star R] [TrivialStar R] {A : Matrix n n R} (hA : A.IsHermitian) : A.IsSymm := by
  rw [IsSymm, ← conjTranspose_eq_transpose_of_trivial, hA.eq]

lemma Matrix.IsHermitian.mulVec_dotProduct_comm_of_trivial {n R : Type*} [Fintype n]
    [CommRing R] [Star R] [TrivialStar R] {A : Matrix n n R} (hA : A.IsHermitian) (x y : n → R) :
    (A.mulVec x) ⬝ᵥ y = x ⬝ᵥ (A.mulVec y) := hA.toSymm_of_trivial.mulVec_dotProduct_comm _ _
