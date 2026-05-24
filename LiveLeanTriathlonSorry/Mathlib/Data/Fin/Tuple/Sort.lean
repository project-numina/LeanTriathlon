/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Data.Fin.Tuple.Sort

@[expose] public section

namespace Tuple

variable {n : ℕ}

theorem perm_ofPerm (p : Equiv.Perm (Fin n)) : Tuple.sort p = p⁻¹ := by
  apply Eq.symm (Tuple.eq_sort_iff.2 ⟨?_, ?_⟩)
  · intro _ _ _
    simpa
  · intro _ _ _ _
    simp_all [(Equiv.bijective p⁻¹).1 ((Equiv.bijective p).1 _)]

end Tuple
