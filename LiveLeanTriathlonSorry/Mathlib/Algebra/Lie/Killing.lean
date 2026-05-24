/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Trace

@[expose] public section

lemma LinearMap.trace_lie_lie (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    (a b c : Module.End R M) : trace R M (⁅a, b⁆ * c) = trace R M (a * ⁅b, c⁆) := by
  rw [show ⁅a, b⁆ = a * b - b * a from LieRing.of_associative_ring_bracket a b,
    show ⁅b, c⁆ = b * c - c * b from LieRing.of_associative_ring_bracket b c]
  rw [sub_mul, map_sub, mul_sub, ← mul_assoc, map_sub]
  congr 1
  rw [← mul_assoc, LinearMap.trace_mul_comm (g := b), mul_assoc]
