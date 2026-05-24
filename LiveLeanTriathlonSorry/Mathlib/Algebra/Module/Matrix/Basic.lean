/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import LiveLeanTriathlonSorry.Mathlib.Algebra.Module.Matrix.Defs
public import LiveLeanTriathlonSorry.Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

lemma Matrix.eigenspace_eq_ker {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (r : R) : A.eigenspace r = LinearMap.ker (A.toLin' - r • LinearMap.id) := by
  ext; simp [sub_eq_zero]

section

attribute [-simp] Submodule.mk_eq_bot

lemma Matrix.hasEigenvalue_iff {R n : Type*} [CommRing R] [Fintype n] (A : Matrix n n R) (r : R) :
    A.HasEigenValue r ↔ ∃ v : n → R, v ≠ 0 ∧ A.mulVec v = r • v := by
  simp [Matrix.HasEigenValue, Submodule.ne_bot_iff, and_comm]

lemma Matrix.hasEigenvalue_iff' {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (r : R) : A.HasEigenValue r ↔ (Module.End.HasEigenvalue A.toLin') r := by
  simp [Matrix.HasEigenValue, Module.End.hasEigenvalue_iff, Submodule.ne_bot_iff]

lemma Matrix.GeneralLinearGroup.hasEigenvalue_iff {R n : Type*} [CommRing R] [Fintype n]
    [DecidableEq n] (u : GL n R) (r : R) :
    u.1.HasEigenValue r ↔ Module.End.HasEigenvalue (M := n → R)
    (u.1.toLinearEquiv' inferInstance) r := by
  simp [Matrix.HasEigenValue, Module.End.hasEigenvalue_iff, Submodule.ne_bot_iff]

end

theorem Matrix.GeneralLinearGroup.inv_eigenvalue {R n : Type*} [CommRing R] [Fintype n]
    [DecidableEq n] (u : GL n R) (r : Rˣ) (hf : u.1.HasEigenValue r) : u⁻¹.1.HasEigenValue r⁻¹.1 :=
  Matrix.GeneralLinearGroup.hasEigenvalue_iff u⁻¹ r⁻¹.1 |>.2 <| Module.End.inv_eigenvalue
  r (u.1.toLinearEquiv' inferInstance) <| Matrix.GeneralLinearGroup.hasEigenvalue_iff u r |>.1 hf

theorem Matrix.GeneralLinearGroup.inv_eigenvalue_iff {R n : Type*} [CommRing R] [Fintype n]
    [DecidableEq n] (u : GL n R) (r : Rˣ) :
    u.1.HasEigenValue r ↔ u⁻¹.1.HasEigenValue r⁻¹.1 :=
  ⟨fun h ↦ Matrix.GeneralLinearGroup.inv_eigenvalue u r h,
  fun h ↦ by convert Matrix.GeneralLinearGroup.inv_eigenvalue _ _ h⟩
