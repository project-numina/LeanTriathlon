/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib
public import LiveLeanTriathlonSorry.Mathlib.RingTheory.Polynomial.Pochhammer
public import LiveLeanTriathlonSorry.Mathlib.RingTheory.Binomial
public import LiveLeanTriathlonSorry.Mathlib.Data.Fin.Tuple.Sort
public import LiveLeanTriathlonSorry.Util.Attributes
@[expose] public section

section Main

universe u v
noncomputable section

open Nat Function Set Equiv Fin

def S : (n : ℕ) → ℕ → Set (Perm (Fin n))
  | zero => fun k ↦ if k = 0 then univ else ∅
  | (Nat.succ n) =>
    fun k ↦
    {p : Perm (Fin (n + 1)) | {s : (Fin n) | p s.castSucc < p s.succ}.ncard = k}

def EulerianNumber : ℕ → ℕ → ℕ :=
  fun n k ↦ (S n k).ncard

variable {R : Type u} [Ring R] [BinomialRing R]

@[AMS 05]
theorem worpitzky (n : ℕ) (x : R) :
    ∑ k ∈ Finset.range (n + 1), (↑(EulerianNumber n k) : R) * Ring.choose (x + k) n = x ^ n := by sorry

end

end Main
