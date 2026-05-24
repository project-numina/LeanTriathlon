/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.RingTheory.Localization.Integer

@[expose] public section

namespace IsLocalization

theorem isInteger_neg {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {a : S}
    (ha : IsInteger R a): IsInteger R (-a) :=
  ⟨- ha.choose, (algebraMap R S).map_neg _ ▸ congr_arg _ ha.choose_spec⟩

theorem isInteger_pow {R S: Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] {a : S}
    (ha : IsInteger R a) (n : ℕ) : IsInteger R (a ^ n) :=
  Nat.recAux (pow_zero a ▸ isInteger_one) (fun _ ih ↦ pow_succ a _ ▸ (isInteger_mul ih ha)) n

lemma _root_.Rat.isInteger_of_exists_integer (q : ℚ) : IsInteger ℤ q ↔ ∃ x : ℤ, x = q := Iff.rfl

lemma _root_.Rat.isInteger_of_Nat (n : ℕ) : IsInteger ℤ (n : ℚ) := ⟨n, by norm_cast⟩

lemma _root_.Finset.sum_IsInteger' {ι} (R R': Type*) [CommSemiring R]
    [CommSemiring R'] [Algebra R R'] (f : ι → R') (S) (h : ∀ i ∈ S, IsInteger R (f i)) :
    IsInteger R (∑ i ∈ S, f i) :=
  ⟨∑ i : S, (h i.1 i.2).choose, by
    simpa using Finset.sum_bij (fun ⟨a, ha⟩ ha' ↦ a)
      (by simp) (by simp) (by simp) (fun i ↦ by simp_all [(h i.1 i.2).choose_spec])⟩

lemma _root_.Finset.sum_IsInteger {ι} [Fintype ι] (R R': Type*) [CommSemiring R]
    [CommSemiring R'] [Algebra R R'] (f : ι → R') (h : ∀ i : ι, IsInteger R (f i)) :
    IsInteger R (∑ i, f i) := Finset.sum_IsInteger' R R' f _ (by simp_all)

lemma _root_.Rat.isInteger_of_dvd (n d : ℤ) (hd : d ∣ n) :
    IsInteger ℤ (n / d : ℚ) :=
  ⟨n / d, by simp only [algebraMap_int_eq, eq_intCast]; aesop⟩

theorem IsInteger_one_div_mul_of_dvd (n : ℕ) (x : ℤ) (hab : x ∣ n) (ha : 0 < x) :
    IsInteger ℤ (1 / x * n : ℚ) :=
  ⟨n / x, by simpa only [one_div_mul_eq_div] using Int.cast_div hab (by aesop)⟩

end IsLocalization
