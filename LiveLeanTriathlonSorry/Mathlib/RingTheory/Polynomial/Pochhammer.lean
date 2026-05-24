/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Polynomial.Smeval
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.RingTheory.Binomial

@[expose] public section

universe u v

noncomputable section

open Nat Function Set Equiv Fin

variable {R : Type u} [Ring R] [BinomialRing R]

open Polynomial in
theorem descPochhammer_succ_smeval {R : Type u} [Ring R] (n : ℕ) (k : R) :
    (descPochhammer ℤ (n + 1)).smeval k = (descPochhammer ℤ n).smeval k * (k - n) := by
  rw [descPochhammer_succ_right, mul_sub, smeval_sub, smeval_mul_X, ← Nat.cast_comm, ← C_eq_natCast,
    smeval_C_mul, zsmul_eq_mul, Int.cast_natCast, Nat.cast_comm, ← mul_sub]

theorem descPochhammer_commute {R : Type u} [Ring R] {k : ℕ} {r r' : R} (h : Commute r r') :
    Commute ((descPochhammer ℤ k).smeval r) r' := by
  induction k
  · simp only [descPochhammer_zero, Polynomial.smeval_one, pow_zero, one_smul, Commute.one_left]
  · rename_i _ h'
    unfold Commute SemiconjBy at h' ⊢
    rw [descPochhammer_succ_smeval, ← mul_assoc, ← h', mul_assoc, mul_sub, mul_assoc, ← h,
      mul_assoc, ← mul_sub, sub_mul, cast_comm]
