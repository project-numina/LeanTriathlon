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

open Filter Topology Asymptotics Real

@[AMS 26]
theorem tauberian {a : ℕ → ℝ} (ha : 0 ≤ a)
    (h : (fun (y : ℝ) ↦ ∑' k : ℕ, a k * rexp (-k * y)) ~[𝓝[>] 0] (fun (y : ℝ) ↦ 1 / y)) :
    (fun n ↦ ∑ k ∈ Finset.range n, a k) ~[atTop] (fun n ↦ ↑n) := sorry

end Main
