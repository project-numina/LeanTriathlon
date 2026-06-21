/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Mathlib.Data.Matrix.Mul

@[expose] public section

open Matrix

variable {R : Type} [Ring R] {n : ℕ}

/--
A quadratic form, represented as a matrix, takes a particular value for some integer vector input
-/
def Matrix.TakesValue (M : Matrix (Fin n) (Fin n) R) (m : ℕ) : Prop :=
  ∃ v : Fin n → ℤ, (fun i => (v i : R)) ⬝ᵥ (M *ᵥ (fun i => (v i : R))) = (m : R)

/--
A quadratic form, represented as a matrix, is universal if it takes every positive integer value.
-/
def Matrix.Universal (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ m : ℕ, 0 < m → M.TakesValue m

/--
A quadratic form is integral if it takes only integer values on integer vectors.
-/
def Matrix.Integral (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ v : Fin n → ℤ,
    (fun i => (v i : R)) ⬝ᵥ (M *ᵥ (fun i => (v i : R))) ∈ Set.range ((↑) : ℤ → R)
