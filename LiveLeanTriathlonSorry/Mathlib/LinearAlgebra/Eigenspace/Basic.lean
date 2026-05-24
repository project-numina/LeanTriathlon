/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.PicardGroup

@[expose] public section

theorem Module.End.inv_eigenvalue {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (r : Rˣ) (f : M ≃ₗ[R] M) (hf : Module.End.HasEigenvalue f.toLinearMap r) :
    Module.End.HasEigenvalue f⁻¹.toLinearMap r⁻¹.1 := by
  obtain ⟨x, hx1, hx2⟩ := Submodule.ne_bot_iff _ |>.1 <| hasEigenvalue_iff.1 hf
  simp only [mem_genEigenspace_one, LinearEquiv.coe_coe] at hx1
  apply_fun f⁻¹ at hx1
  erw [LinearEquiv.symm_apply_apply, map_smul] at hx1
  apply_fun (r⁻¹.1 • · ) at hx1
  rw [← mul_smul, Units.inv_mul, one_smul] at hx1
  exact Submodule.ne_bot_iff _ |>.2 ⟨x, by simpa using hx1.symm, hx2⟩

theorem Module.End.inv_eigenvalue_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (r : Rˣ) (f : M ≃ₗ[R] M) : Module.End.HasEigenvalue f.toLinearMap r ↔
    Module.End.HasEigenvalue f⁻¹.toLinearMap r⁻¹.1 :=
  ⟨fun h ↦ Module.End.inv_eigenvalue _ _ h, fun h ↦ by convert Module.End.inv_eigenvalue _ _ h⟩

theorem Module.End.inv_eigenvalue' (K M : Type*) [Field K] [AddCommGroup M] [Module K M]
    (r : K) (f : M ≃ₗ[K] M) (hf : Module.End.HasEigenvalue f.toLinearMap r) :
    Module.End.HasEigenvalue f⁻¹.toLinearMap r⁻¹ := by
  classical
  if hr : r = 0 then subst hr; simp_all [hasEigenvalue_iff] else
  simpa using Module.End.inv_eigenvalue (Units.mk0 r hr) f hf

theorem Module.End.inv_eigenvalue_iff' (K M : Type*) [Field K] [AddCommGroup M] [Module K M]
    (r : K) (f : M ≃ₗ[K] M) : Module.End.HasEigenvalue f.toLinearMap r ↔
    Module.End.HasEigenvalue f⁻¹.toLinearMap r⁻¹ := by
  classical
  if hr : r = 0 then subst hr; simp_all [hasEigenvalue_iff] else
  simpa using Module.End.inv_eigenvalue_iff (Units.mk0 r hr) f

section Add

open Matrix

variable {n : ℕ}

lemma hasEigenvalue_one_add (M : Matrix (Fin n) (Fin n) ℂ) (γ : ℂ)
    (h : Module.End.HasEigenvalue (toLin' M) γ) :
    Module.End.HasEigenvalue (toLin' (1 + M)) (1 + γ) := by
  rw [Module.End.hasEigenvalue_iff_mem_spectrum] at h ⊢
  have h1 : toLin' (1 + M) = toLin' 1 + toLin' M := toLin'.map_add 1 M
  rw [h1, toLin'_one]
  have h2 : LinearMap.id = (algebraMap ℂ (Module.End ℂ (Fin n → ℂ))) 1 := by
    ext v
    simp [Algebra.algebraMap_eq_smul_one]
  rw [h2, ← spectrum.singleton_add_eq]
  exact Set.add_mem_add (Set.mem_singleton 1) h

lemma LinearMap.hassEigenvalue_iff_sub_zero_char {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (r : R) (f : Module.End R M) : Module.End.HasEigenvalue f r ↔
    Module.End.HasEigenvalue (f - r • 1) 0 := by
  simp [Module.End.hasEigenvalue_iff, Module.End.eigenspace_def]

lemma hasEigenvalue_sub_scalar (M : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ)
    (hμ : Module.End.HasEigenvalue (toLin' M) μ) :
    Module.End.HasEigenvalue (toLin' (M - μ • 1)) 0 := by
  rw [Module.End.hasEigenvalue_iff] at hμ ⊢
  contrapose! hμ

  have h_eq : Module.End.eigenspace (toLin' M) μ =
      Module.End.eigenspace (toLin' (M - μ • 1)) 0 := by
    ext v
    simp only [Module.End.mem_eigenspace_iff, zero_smul]
    constructor
    · intro hv
      have : toLin' (μ • 1) v = μ • v := by simp
      calc toLin' (M - μ • 1) v
          = toLin' M v - toLin' (μ • 1) v := by rw [map_sub, LinearMap.sub_apply]
        _ = μ • v - μ • v := by rw [hv, this]
        _ = 0 := sub_self _
    · intro hv
      have : toLin' (μ • 1) v = μ • v := by simp
      have h_sub : toLin' M v - toLin' (μ • 1) v = 0 := by
        rw [map_sub, LinearMap.sub_apply] at hv
        exact hv
      have : toLin' M v = μ • v := by
        rw [sub_eq_zero] at h_sub
        rw [h_sub, this]
      exact this
  rw [h_eq]
  exact hμ

end Add
