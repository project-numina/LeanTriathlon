/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Mathlib.Data.ENNReal.Operations

@[expose] public section

open scoped NNReal ENNReal

namespace ENNReal

@[simp]
theorem sSup_range_coe : sSup (Set.range ((↑) : ℝ≥0 → ℝ≥0∞)) = ⊤ := by
  rw [sSup_eq_top]
  intro b hb
  exact ⟨↑(b.toNNReal + 1), Set.mem_range_self _, by
    rw [ENNReal.coe_add, ENNReal.coe_toNNReal hb.ne, ENNReal.coe_one]
    exact ENNReal.lt_add_right hb.ne one_ne_zero⟩

end ENNReal
