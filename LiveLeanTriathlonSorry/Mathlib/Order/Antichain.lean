/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey and Numina team
-/
module

public import Mathlib.Order.Antichain

@[expose] public section

variable {P : Type*} [PartialOrder P]

lemma IsAntichain_empty : IsAntichain (· ≤ ·) (∅ : Set P) := by
  simp [IsAntichain]
