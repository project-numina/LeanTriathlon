/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.RingTheory.SimpleRing.Principal
public import LiveLeanTriathlonSorry.Util.Attributes
public import LiveLeanTriathlonSorry.Mathlib.Data.Multiset.Fintype
@[expose] public section

section Main

open Polynomial

@[AMS 30]
theorem Complex.mem_convexHull_roots_of_mem_derivative_roots (p : ℂ[X]) (z : ℂ)
    (z_mem_roots_p_derivative : z ∈ p.derivative.roots) :
    z ∈ convexHull ℝ (p.roots.toFinset : Set ℂ) := sorry

end Main
