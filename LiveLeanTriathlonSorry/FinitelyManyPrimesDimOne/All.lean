/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import LiveLeanTriathlonSorry.Util.Attributes
@[expose] public section

section Background

open Ideal

variable {R : Type*} [CommRing R]

instance PrimeSpectrum.finite_quotient [Finite (PrimeSpectrum R)] (I : Ideal R) :
    Finite (PrimeSpectrum (R ⧸ I)) :=
  Finite.of_injective (PrimeSpectrum.comap (Ideal.Quotient.mk I))
    (PrimeSpectrum.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective)

end Background

section Main

open Ideal

variable {R : Type*} [CommRing R]

@[stacks 0ALV, AMS 13]

theorem Ring.krullDimLE_one_of_finite_primeSpectrum
    [IsNoetherianRing R] [Finite (PrimeSpectrum R)] :
    Ring.KrullDimLE 1 R := by sorry

end Main
