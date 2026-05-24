/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Int.Star
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import LiveLeanTriathlonSorry.Mathlib.NumberTheory.FactorisationProperties
public import LiveLeanTriathlonSorry.Util.Attributes
@[expose] public section

section Main

open Nat ArithmeticFunction.sigma

section Definitions

def Nat.oddPart (n : ℕ) : ℕ := ordCompl[2] n

end Definitions

section HelperLemmas

end HelperLemmas

section MainTheorem

@[AMS 11]
theorem weird_squarefree_infinite : ∀ N, ∃ n > N, Weird n ∧ ¬ Squarefree (n.oddPart) := by sorry

end MainTheorem

end Main
