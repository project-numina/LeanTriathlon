/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

lemma Fin.prod_div_succ {α} [CommGroupWithZero α] {n : ℕ} {f : Fin (n + 1) → α}
    (hf : ∀ i, f i ≠ 0) : ∏ i : Fin n, f i.succ / f i.castSucc = f (Fin.last n) / f 0 := by
  induction n with
  | zero => simp [div_self (hf 0)]
  | succ n ih =>
  have h' := by simpa [-Finset.prod_div_distrib] using @ih (f ∘ Fin.castSucc) (by simp [hf])
  rw [Fin.prod_univ_castSucc, h', mul_comm, div_mul_div_cancel₀ (by grind), Fin.succ_last]

lemma Finset.sum_sub_succ_cancel {α n} [AddCommGroup α] (f : Fin (n + 1) → α) (i : Fin (n + 1)) :
    ∑ j : Fin n with j.castSucc < i, (f j.succ - f j.castSucc) = f i - f 0 := by
  induction hi : i.val generalizing i with
  | zero => simp [show i = 0 by ext; simp [hi]]
  | succ m ih =>
    if hn : n = 0 then subst hn; simp [@Subsingleton.elim (Fin 1) _ i 0] else
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hi' : 1 ≤ i := by rw [Fin.le_def, hi, Fin.val_one]; omega
    have hs : Finset.univ.filter (fun j : Fin (n' + 1) ↦ j.castSucc < i) = insert ⟨i - 1, by grind⟩
      (Finset.univ.filter (fun j ↦ j.castSucc < i - 1)) := Finset.ext fun x ↦ by
      simp only [Fin.lt_def, Fin.val_castSucc, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.sub_val_of_le hi', Fin.coe_ofNat_eq_mod, Nat.one_mod, Finset.mem_insert, Fin.ext_iff]
      convert (propext or_comm) ▸ x.1.lt_succ_iff_lt_or_eq (n := i.1 - 1)
      grind
    rw [hs, Finset.sum_insert (by simp [Fin.le_def, Fin.sub_val_of_le hi']), ih (i - 1)
      (by rw [Fin.sub_val_of_le  hi', Fin.val_one]; omega)]
    simp only [Fin.succ_mk, i.1.sub_one_add_one (by omega), ← Fin.eq_mk_iff_val_eq.2 rfl,
      Fin.castSucc_mk]
    simp_rw [← Fin.val_one n', ← Fin.sub_val_of_le hi', ← Fin.eq_mk_iff_val_eq.2 rfl]
    rw [add_sub]
    simp only [Fin.coe_ofNat_eq_mod, sub_left_inj]
    exact sub_add_cancel (f i) (f (i - 1))
