/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Algebra.Lie.Solvable
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

open Module in
theorem LiesTheorem (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (L : LieSubalgebra ℂ (Module.End ℂ V)) [hL : LieAlgebra.IsSolvable L] :
    let n := finrank ℂ V
    ∃ B : Basis (Fin n) ℂ V, ∀ l ∈ L, (l.toMatrix B B).BlockTriangular id := by

  induction (finrank ℂ V) with
  | zero =>
    have : Subsingleton V := Module.finrank_zero_iff (R := ℂ).1 <| by sorry
    refine ⟨Module.Basis.empty V, sorry⟩
  | succ n _ => sorry
