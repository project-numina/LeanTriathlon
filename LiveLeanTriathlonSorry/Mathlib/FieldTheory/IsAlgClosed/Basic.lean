/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

lemma Polynomial.roots_zero_iff {K : Type*} [Field K] [IsAlgClosed K] {p : Polynomial K} :
    (∀ x ∈ p.roots, x = 0) ↔ ∃ a : K, p = a • Polynomial.X ^ p.natDegree :=
  ⟨fun hp ↦ by
  have hp' := Splits.eq_prod_roots <| IsAlgClosed.splits p
  refine ⟨p.leadingCoeff, ?_⟩
  have : (Multiset.map (fun a ↦ X - C a) p.roots) = Multiset.replicate p.natDegree X :=
  Multiset.eq_replicate.2 ⟨by simpa using Polynomial.splits_iff_card_roots.1 <| IsAlgClosed.splits p,
    fun y hy ↦ by obtain ⟨z, hz1, hz2⟩ := Multiset.mem_map.1 hy; simpa [hp z hz1] using hz2.symm⟩
  simp only [this, Multiset.prod_replicate] at hp'
  nth_rw 1 [hp', smul_eq_C_mul], fun ⟨a, ha⟩ x ↦ by
  if ha' : a = 0 then simp_all +singlePass else
  rw [ha, Polynomial.smul_eq_C_mul, roots_C_mul_X_pow ha'] ; simp⟩

lemma Polynomial.roots_zero_iff' {K : Type*} [Field K] [IsAlgClosed K] {p : Polynomial K}
    (hp : p.Monic) : (∀ x ∈ p.roots, x = 0) ↔ p = X ^ p.natDegree :=
  propext (Polynomial.roots_zero_iff (p := p)) ▸ ⟨fun ⟨a, ha⟩ ↦ by
  nth_rw 1 [ha, smul_eq_C_mul]
  simp only [ne_eq, pow_eq_zero_iff', X_ne_zero, false_and, not_false_eq_true, mul_eq_right₀]
  have : p.leadingCoeff = _ := congr((coeff $ha) p.natDegree)
  simp only [hp, Monic.leadingCoeff, coeff_smul, coeff_X_pow, ↓reduceIte, smul_eq_mul,
    mul_one] at this
  simp [this.symm], fun hp' ↦ ⟨1, by simp_all +singlePass⟩⟩
