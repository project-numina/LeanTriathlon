/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Tactic.NormNum.GCD
public import LiveLeanTriathlonSorry.Util.Attributes
@[expose] public section

section Main
assert_not_exists Module.End.inv_eigenvalue_iff Matrix.GeneralLinearGroup.inv_eigenvalue

@[AMS 15]
theorem Module.End.inv_eigenvalue_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (r : Rˣ) (f : M ≃ₗ[R] M) : Module.End.HasEigenvalue f.toLinearMap r ↔
    Module.End.HasEigenvalue f⁻¹.toLinearMap r⁻¹.1 := by sorry

end Main
