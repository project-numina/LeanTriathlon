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

open Real PMF BigOperators ENNReal NNReal Finset
noncomputable section

open scoped Classical

section Finset

universe u v

end Finset

section Binomial

def PMF.apply_NNReal {α : Type} (p : PMF α) (a : α) : NNReal :=
  ENNReal.toNNReal (p a)

end Binomial

section Definitions

def jury_majority_decision_probability (p : NNReal) (hp : p ≤ 1) (n : ℕ) : NNReal :=
  ((PMF.binomial p hp (2 * n + 1)).map (fun k => if k > n then true else false)).apply_NNReal true

end Definitions

section MainTheorem

def condorcet_extra (p : NNReal) (n : ℕ) : NNReal :=
  ((2 * n + 1).choose n : ℕ) * (p * (1 - p))^(n+1) * (p - (1 - p))

def B_term (p : NNReal) (n : ℕ) : NNReal :=
  ((2 * n + 1).choose n : ℕ) * p^n * (1 - p)^(n + 1)

def B_term_succ (p : NNReal) (n : ℕ) : NNReal :=
  ((2 * n + 1).choose n : ℕ) * p^(n + 1) * (1 - p)^n

@[AMS 60]
theorem condorcet_jury_theorem (p : NNReal) (hp : p ≤ 1) (hp' : 1/2 < p) (hp_lt : p < 1)
    (n m : ℕ) (n_lt_m : n < m) :
    jury_majority_decision_probability p hp n < jury_majority_decision_probability p hp m := by sorry

end MainTheorem

end

end Main
