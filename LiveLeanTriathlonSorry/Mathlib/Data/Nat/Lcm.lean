/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import LiveLeanTriathlonSorry.Mathlib.RingTheory.Localization.Integer
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Analysis.Normed.Field.Lemmas

@[expose] public section

namespace Nat

def LCM : ℕ → ℕ
  | 0 => 1
  | n + 1 => lcm (n + 1) (LCM n)

@[simp]
lemma LCM_of_zero : LCM 0 = 1 := rfl

@[simp]
lemma LCM_of_pos {a : ℕ} (ha : 0 < a) : LCM a = lcm a (LCM (a - 1)) := by
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha); simp [LCM]

lemma LCM_pos (n : ℕ) : 0 < LCM n := Nat.recAux zero_lt_one (fun n ih ↦ (lcm_pos (succ_pos n) ih)) n

public meta section PositivityExtension

open Lean Meta Mathlib Meta Positivity Qq in

@[positivity Nat.LCM _]
meta def evalLCM : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Nat.LCM $a) =>
    assertInstancesCommute
    return .positive q(Nat.LCM_pos $a)
  | _, _, _ => throwError "not Nat.LCM"

end PositivityExtension

lemma LCM_dvd_LCM {a b : ℕ} (hab : a ≤ b) : LCM a ∣ LCM b := le_induction (Nat.dvd_refl a.LCM)
  (fun n _ ih ↦ dvd_trans ih (dvd_lcm_right (n + 1) n.LCM)) b hab

lemma LCM_le_LCM {a b : ℕ} (hab : a ≤ b) : LCM a ≤ LCM b := le_of_dvd (LCM_pos b) (LCM_dvd_LCM hab)

lemma dvd_LCM {a : ℕ} (ha : 0 < a) : a ∣ LCM a := by simpa [ha] using dvd_lcm_left _ _

lemma dvd_LCM_of_le {a b : ℕ} (hab : a ≤ b) (ha : 0 < a) : a ∣ LCM b :=
  (dvd_LCM ha).trans (LCM_dvd_LCM hab)

open IsLocalization in
theorem one_div_mul_LCM_IsInteger (b : ℕ) (x : ℤ) (hab : x ≤ b) (ha : 0 < x) :
    IsLocalization.IsInteger ℤ (1 / x * b.LCM : ℚ) := by
  obtain ⟨c, hc⟩ := @dvd_LCM_of_le x.natAbs b (by grind) (by grind)
  exact IsInteger_one_div_mul_of_dvd _ _ ⟨c, by simpa [hc, Nat.cast_mul] using by grind⟩ ha

lemma isInteger_one_dvd_mul_LCM (a : ℚ) (b : ℕ) (hab : a ≤ b) (ha : 0 < a)
    (h_a_isInteger : IsLocalization.IsInteger ℤ a): IsLocalization.IsInteger ℤ (1 / a * LCM b) := by
  obtain ⟨x, hx⟩ := h_a_isInteger
  simpa [← hx] using one_div_mul_LCM_IsInteger b x (Rat.intCast_le_intCast.1 (by simp_all)) <|
    Rat.intCast_pos.1 <| by simp_all
