/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib
public import LiveLeanTriathlonSorry.Util.Attributes
@[expose] public section

section Main

open Matrix

open Submodule

variable {K : Type*} [Field K]

variable {m n : ℕ}

structure SystemOfLinearEquations (K : Type*) [Field K] (m n : ℕ) where
  A : Matrix (Fin m) (Fin n) K
  b : Fin m → K

def AugmentedMatrix {K : Type*} [Field K] {m n : ℕ}
    (sys : SystemOfLinearEquations K m n) : Matrix (Fin m) (Fin (n + 1)) K :=
  Matrix.of (fun i j => if h : j.val < n then sys.A i ⟨j.val, h⟩ else sys.b i)

def ColumnSpace {K : Type*} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) :
    Submodule K (Fin m → K) :=
  Submodule.span K (Set.range (fun j : Fin n => A.transpose j))

noncomputable def MatrixRank {K : Type*} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) : ℕ :=
  Module.finrank K (ColumnSpace A)

@[AMS 15]
theorem rouche_capelli {K : Type*} [Field K] {m n : ℕ}
    (sys : SystemOfLinearEquations K m n) :
    (∃ x : Fin n → K, sys.A.mulVec x = sys.b) ↔
    MatrixRank sys.A = MatrixRank (AugmentedMatrix sys) := sorry

end Main
