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

open Nat

@[AMS 05]
theorem starofdavid (n k : ℕ) :
    (((n - 1).choose (k - 1)).gcd (n.choose (k + 1))).gcd ((n + 1).choose k)
    = (((n - 1).choose k).gcd (n.choose (k - 1))).gcd ((n + 1).choose (k + 1)) := by sorry

end Main
