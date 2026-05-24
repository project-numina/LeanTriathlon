/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.RingTheory.Binomial
public import LiveLeanTriathlonSorry.Mathlib.RingTheory.Polynomial.Pochhammer

@[expose] public section

universe u v

noncomputable section

open Nat Function Set Equiv Fin

variable {R : Type u} [Ring R] [BinomialRing R]

theorem Ring.choose_commute {k : ℕ} {r r' : R} (h : Commute r r') : Commute (choose r k) r' := by
  apply @IsAddTorsionFree.nsmul_right_injective R
    (by infer_instance) (BinomialRing.toIsAddTorsionFree) (k !) (factorial_ne_zero k)
  simp only [nsmul_eq_mul]
  rw [← mul_assoc, ← mul_assoc, cast_comm _ r', mul_assoc r',
    ← nsmul_eq_mul, ← descPochhammer_eq_factorial_smul_choose, descPochhammer_commute h]

theorem Ring.choose_succ_right_eq (k : ℕ) (x : R) :
    choose x (k + 1) * (k + 1) = choose x k * (x - k) := by
  have e : (x + 1) * choose x k = choose x (k + 1) * (k + 1) + choose x k * (k + 1) := by
    rw[← add_mul, add_comm (choose _ _), ← choose_succ_succ]
    apply @IsAddTorsionFree.nsmul_right_injective R
      (by infer_instance) (BinomialRing.toIsAddTorsionFree) (k !) (factorial_ne_zero k)
    simp only [nsmul_eq_mul]
    rw[← mul_assoc, ← mul_assoc, cast_comm,
      mul_assoc, cast_comm _ (choose (x + 1) (k + 1)), mul_assoc]
    have : ↑k ! * ((↑k : R) + 1) = (k + 1) ! := by
      rw [factorial, succ_eq_add_one, cast_mul, cast_comm, cast_add, cast_one]
    rw [this, ← cast_comm ((k + 1)!), ← nsmul_eq_mul, ← descPochhammer_eq_factorial_smul_choose,
      ← nsmul_eq_mul, ← descPochhammer_eq_factorial_smul_choose,
      Ring.descPochhammer_succ_succ_smeval, descPochhammer_succ_smeval, nsmul_eq_mul',
      ← descPochhammer_commute (by simp), ← mul_add, cast_add, cast_one]
    abel_nf
  rw [← sub_eq_of_eq_add e, ← Ring.choose_commute (by simp), ← mul_sub, add_sub_add_right_eq_sub]
