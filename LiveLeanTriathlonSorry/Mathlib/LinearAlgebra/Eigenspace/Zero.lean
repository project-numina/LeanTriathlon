/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.Data.Rat.Floor
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.RingTheory.SimpleModule.Basic

@[expose] public section

open Polynomial in
lemma LinearMap.charpoly_roots_eq_minpoly {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (u : Module.End K V) (x : K) :
    x ∈ u.charpoly.roots ↔ x ∈ (minpoly K u).roots :=
  have hu : minpoly K u ≠ 0 := minpoly.ne_zero <| IsIntegral.of_finite K u
  ⟨fun hx ↦ by
    simp only [mem_roots', ne_eq, hu, not_false_eq_true, IsRoot.def, true_and]
    simp only [mem_roots', ne_eq, IsRoot.def, LinearMap.eval_charpoly] at hx
    simpa [LinearMap.eval_charpoly, ← IsRoot.def, ← Module.End.hasEigenvalue_iff_isRoot,
      Module.End.hasEigenvalue_iff_mem_spectrum] using fun h ↦
      isUnit_iff_ne_zero.1 (LinearMap.isUnit_det _ h) hx.2,
  fun hx ↦ mem_roots u.charpoly_monic.ne_zero |>.2 <| IsRoot.dvd (mem_roots hu |>.1 hx) <|
    LinearMap.minpoly_dvd_charpoly u⟩

open Polynomial Matrix LinearMap Module.Free

private lemma Matrix.charpoly_sub_scalar' {R : Type*} [CommRing R] {n : Type*}
    [DecidableEq n] [Fintype n] (A : Matrix n n R) (μ : R) :
    (A - scalar n μ).charpoly = A.charpoly.comp (X + C μ) := by
  simp_rw [Matrix.charpoly, det_apply, Polynomial.sum_comp]
  congr! 1 with σ
  rw [show (Equiv.Perm.sign σ • ∏ i, A.charmatrix (σ i) i).comp (X + C μ) =
      Equiv.Perm.sign σ • (∏ i, A.charmatrix (σ i) i).comp (X + C μ) by
      apply Polynomial.smul_comp]
  congr 1
  simp_rw [Polynomial.prod_comp]
  congr! with i _
  by_cases hi : σ i = i <;> simp [hi, charmatrix_apply_eq, charmatrix_apply_ne]
  ring

private lemma LinearMap.charpoly_sub_smul' {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (f : M →ₗ[R] M) (μ : R) :
    (f - μ • 1).charpoly = f.charpoly.comp (X + C μ) := by
  simp only [charpoly_def]
  have h : toMatrix (chooseBasis R M) (chooseBasis R M) (f - μ • 1) =
           toMatrix (chooseBasis R M) (chooseBasis R M) f - scalar _ μ := by
    ext i j
    simp only [map_sub, toMatrix_one, map_smul]
    by_cases hij : i = j <;> simp [hij, scalar, diagonal]
  rw [h]
  exact Matrix.charpoly_sub_scalar' _ _

