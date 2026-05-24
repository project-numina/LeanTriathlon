/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Data.Matrix.Mul

@[expose] public section

@[simp]
def Matrix.eigenspace {R n : Type*} [CommRing R] [Fintype n] (A : Matrix n n R)
    (r : R) : Submodule R (n → R) where
  carrier := {v : n → R | A.mulVec v = r • v}
  add_mem' := by simp +contextual [mulVec_add]
  zero_mem' := by simp
  smul_mem' := by simp +contextual [mulVec_smul, ← SemigroupAction.mul_smul, mul_comm]

def Matrix.HasEigenValue {R n : Type*} [CommRing R] [Fintype n] (A : Matrix n n R) (r : R) :
  Prop := A.eigenspace r ≠ ⊥
