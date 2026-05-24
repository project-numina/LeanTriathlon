/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Rat.Star
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Field
import Mathlib.Tactic.Attr.Register

@[expose] public section

namespace Nat

def binom (a b : ℕ) : ℕ := Nat.choose (a + b) a

@[simp]
lemma binom_eq_choose (a b : ℕ) : binom a b = Nat.choose (a + b) a := rfl

lemma binom_symm (a b : ℕ) : binom a b = binom b a := by
  simpa [add_comm] using choose_symm_add

theorem binom_pos (a b : ℕ) : 0 < binom a b := Nat.choose_pos (le_add_right a b)

theorem binom_eq_factorial_div_factorial (a b : ℕ) : binom a b =
    (a + b)! / (a ! * b !) := by simp [choose_eq_factorial_div_factorial]

theorem Rat.binom_eq_factorial_div_factorial (a b : ℕ) :
    (binom a b : ℚ) = (a + b)! / (a ! * b !) := by
  rw [← Nat.cast_mul, ← Nat.cast_div (factorial_mul_factorial_dvd_factorial_add a b)
    (by simp [factorial_ne_zero])]
  exact congr_arg _ <| Nat.binom_eq_factorial_div_factorial _ _

theorem binom_eq_multinomial (a b : ℕ) :
    binom a b = Nat.multinomial (Finset.univ) ![a, b] := by
  simp [multinomial_univ_two, choose_eq_factorial_div_factorial]

public meta section PositivityExtension

open Lean Meta Mathlib Meta Positivity Qq in

@[positivity binom (_ : ℕ) (_ : ℕ)]
meta def evalBinom : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(binom $a $b) =>
    assertInstancesCommute
    return .positive q(binom_pos $a $b)
  | _, _, _ => throwError "not binom"

end PositivityExtension

lemma add_one_mul_choose_add_one_self (m : ℕ) : (m + 1) * (binom (m + 1) m) =
    (2 * m + 1) * (binom m m) := by
  qify [Rat.binom_eq_factorial_div_factorial]
  simpa [factorial_succ, show (m + 1 + m)! = (2 * m + 1)! by ring_nf, show (m + m)! = (2 * m)! by
    ring_nf] using by field
