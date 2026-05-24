/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
public import LiveLeanTriathlonSorry.Util.Attributes
@[expose] public section

section Main

open Ideal

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]

@[AMS 13]
theorem Ideal.ufd_iff_height_one_primes_principal :
    UniqueFactorizationMonoid R ↔
    ∀ (p : Ideal R) [p.IsPrime], p.primeHeight = 1 → p.IsPrincipal := by sorry

end Main
