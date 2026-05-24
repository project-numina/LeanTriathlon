/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä and Numina team
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

@[simp] lemma memLp_add_const_iff {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (f : X → ℝ) (c : ℝ) (p : ℝ≥0∞) :
    MemLp (f + fun _ ↦ c) p μ ↔ MemLp f p μ := by
  constructor
  · intro Z_add_c_mem_Lp
    convert Z_add_c_mem_Lp.sub (memLp_const c)
    simp
  · intro Z_mem_Lp
    exact Z_mem_Lp.add (memLp_const c)
