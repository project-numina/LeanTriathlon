/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib.Data.Rat.Encodable
public import Mathlib.Analysis.RCLike.Basic
public import LiveLeanTriathlonSorry.Mathlib.Classical
public import LiveLeanTriathlonSorry.Util.Attributes
@[expose] public section

section Main

universe u

open Set Filter Topology

@[AMS 26]
theorem Real.countable_not_continuousAt (f : ℝ → ℝ) (h_mono : Monotone f) :
    {x | ¬ ContinuousAt f x}.Countable := by sorry

end Main
