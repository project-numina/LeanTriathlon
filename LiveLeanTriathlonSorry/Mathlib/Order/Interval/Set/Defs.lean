/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Mathlib.Data.Real.Basic

@[expose] public section

open Real Set

lemma Ioo_union_Ioo_translate_nonneg {a b t : ℝ} (ht_nonneg : 0 ≤ t) (ht : t < b - a) :
    Ioo a b ∪ Ioo (a + t) (b + t) = Ioo a (b + t) := by
  grind

lemma Ioo_union_Ioo_translate_nonpos {a b t : ℝ} (ht_nonpos : t < 0) (ht : -t < b - a) :
    Ioo a b ∪ Ioo (a + t) (b + t) = Ioo (a + t) b := by
  grind
