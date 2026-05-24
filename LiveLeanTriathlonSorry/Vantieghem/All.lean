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

universe u

open Nat Finset BigOperators

namespace Vantieghem

section Forward

end Forward

section Backward

end Backward

end Vantieghem

@[AMS 11]
theorem vantieghem {n : ℕ} (hn : 3 ≤ n) :
    n.Prime ↔ (∏ k ∈ Finset.Ico 1 n, (2 ^ k - 1)) ≡ n [MOD (2 ^ n - 1)] := sorry

end Main
