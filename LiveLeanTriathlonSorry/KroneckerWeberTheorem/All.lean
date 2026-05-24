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

@[AMS 11]
theorem KroneckerWeber (F : Type*) [Field F] [NumberField F] [IsAbelianGalois ℚ F] :
    ∃ n, ∃ (K : Type*) (_ : Field K) (_ : Algebra ℚ K) (_ : Algebra F K) (_ : IsScalarTower ℚ F K),
    IsCyclotomicExtension {n} ℚ K := sorry

end Main
