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

open Nat Finset BigOperators

namespace Wolstenholme

end Wolstenholme

@[AMS 11]
theorem wolstenholme {p : ℕ} (hp : p.Prime) (hp' : 5 ≤ p) :
    (2 * p - 1).choose (p - 1) ≡ 1 [MOD p ^ 3] := by sorry

end Main
