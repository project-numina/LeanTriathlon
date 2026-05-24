/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

lemma ZMod.val_add_eq {p : ℕ} [NeZero p] (a b : ZMod p) :
    ∃ k : ℕ, (a + b).val + k * p = a.val + b.val :=
  ZMod.val_add a b ▸ ⟨((a.val + b.val) / p : ℕ), Nat.mod_add_div' ..⟩

lemma ZMod.cast_add_eq' {p : ℕ} [NeZero p] (a b : ZMod p) :
    ∃ k : ℤ, (a + b).cast + k * p = a.cast + b.cast := by
  simp only [cast_eq_val]
  exact ⟨ZMod.val_add_eq a b|>.choose, by exact_mod_cast ZMod.val_add_eq a b|>.choose_spec⟩

lemma ZMod.cast_add_eq {p : ℕ} [NeZero p] (a b : ZMod p) :
    ∃ k : ℤ, (a + b).cast = a.cast + b.cast + k * p := by
  obtain ⟨k, hk⟩ := ZMod.cast_add_eq' a b
  exact ⟨-k, by grind⟩

lemma Finset.sum_ZMod_cast {ι : Type*} {p : ℕ} [NeZero p] {f : ι → ZMod p} {s : Finset ι} :
    ∃ k : ℤ, (∑ i ∈ s, f i).cast = ∑ i ∈ s, (f i).cast + k * p := by
  classical
  induction s using Finset.induction_on with
  | empty => use 0; simp
  | insert a s ha ih =>
    simp [Finset.sum_insert ha]
    obtain ⟨k0, hk0⟩ := ZMod.cast_add_eq (f a) (∑ i ∈ s, f i)
    obtain ⟨k1, hk1⟩ := ih
    refine ⟨k0 + k1, ?_⟩
    simp_all
    ring

lemma ZMod.cast_mul_eq_sub {p : ℕ} [NeZero p] (a b : ZMod p) :
    ((a * b).cast : ℤ) = a.cast * b.cast - (a.val * b.val / p) * p := by
  simp_rw [ZMod.cast_eq_val]
  rw [ZMod.val_mul]
  rw [eq_comm, sub_eq_iff_eq_add, eq_comm]
  exact_mod_cast Nat.mod_add_div' ..

lemma ZMod.cast_coe_intCast {p : ℕ} (a : ℤ) :
    (ZMod.cast (a : ZMod p) : ℤ) + a / p * p = a  := by
  rw [ZMod.coe_intCast]
  exact mul_comm (p : ℤ) _ ▸ Int.emod_add_mul_ediv a p
