/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Order.Antichain
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Find
public import Mathlib.Algebra.Order.Group.Nat

@[expose] public section

namespace PartialOrder

open Classical Finset Nat

universe u

variable {P : Type u} [PartialOrder P]

open Classical in

noncomputable def width (S : Finset P) : ℕ :=
  Nat.findGreatest
    { n | ∃ (s : Finset P), s ⊆ S ∧ IsAntichain (· ≤ ·) (SetLike.coe s) ∧ s.card = n }
    S.card

lemma Nat.findGreatest_isGreatest_of_le {P : ℕ → Prop} [DecidablePred P] (n k : ℕ) (hk1 : P k)
    (hk2 : k ≤ n) : IsGreatest {m | P m ∧ m ≤ n} (Nat.findGreatest P n) where
  left := ⟨Nat.findGreatest_spec hk2 hk1, Nat.findGreatest_le _⟩
  right := mem_upperBounds.2 <| by simpa using fun _ hx1 hx2 ↦ Nat.le_findGreatest hx2 hx1

open scoped Classical in
lemma Nat.findGreatest_isGreatest_of_le' {P : ℕ → Prop} (n k : ℕ) (hk1 : P k)
    (hk2 : ∀ m, P m → m ≤ n): IsGreatest {m | P m} (Nat.findGreatest P n) :=
  (by ext; grind : {m | P m} = {m | P m ∧ m ≤ n}) ▸
  Nat.findGreatest_isGreatest_of_le n k hk1 (hk2 k hk1)

lemma width_spec (S : Finset P) :
  IsGreatest { n | ∃ (s : Finset P), s ⊆ S ∧ IsAntichain (· ≤ ·) (SetLike.coe s) ∧ s.card = n }
    (width S) :=
  Nat.findGreatest_isGreatest_of_le' _ 0
    (by simp) (by simpa using fun _ s hs1 _ hs3 ↦ hs3 ▸ card_le_card hs1)

lemma exists_antichain_of_width (S : Finset P) :
    ∃ (s : Finset P), s ⊆ S ∧ IsAntichain (· ≤ ·) (SetLike.coe s) ∧ s.card = width S :=
  (width_spec S).1

lemma width_le_of_exists_antichain (S : Finset P) (s : Finset P)
    (hs_subset : s ⊆ S) (hs_antichain : IsAntichain (· ≤ ·) (SetLike.coe s)) :
    s.card ≤ width S :=
  mem_upperBounds.1 (width_spec S).2 s.card ⟨s, hs_subset, hs_antichain, rfl⟩

@[simp]
lemma width_empty : width (∅ : Finset P) = 0 := by
  simp [width, Finset.card_empty]

open scoped Classical in

lemma width_erase_le (S : Finset P) (a : P) : width (S.erase a) ≤ width S := by
  obtain ⟨s, hs_sub_erase, hs_anti, hs_card⟩ := width_spec (S.erase a)|>.1
  exact hs_card.symm ▸ mem_upperBounds.1 (width_spec S).2 s.card <| by simpa using
    ⟨s, hs_sub_erase.trans (Finset.erase_subset a S), hs_anti, hs_card⟩

open scoped Classical in
lemma width_le_of_subset (S T : Finset P) (hST : S ⊆ T) : width S ≤ width T :=
  Nat.findGreatest_mono (by simpa [setOf] using fun _ s hs1 hs2 hs3 ↦
    ⟨s, hs1.trans hST, hs2, hs3⟩) <| card_le_card hST

open scoped Classical in

lemma width_erase_ge (S : Finset P) (a : P) : width S ≤ width (S.erase a) + 1 := by
  obtain ⟨A, hA_sub, hA_anti, hA_card⟩ := width_spec S |>.1
  if ha : a ∈ A then exact Nat.le_add_of_sub_le <| hA_card ▸ Finset.card_erase_of_mem ha ▸
    mem_upperBounds.1 (width_spec (S.erase a)).2 (A.erase a).card ⟨(A.erase a),
    erase_subset_erase a hA_sub, by simp_all [IsAntichain, Set.Pairwise], rfl⟩ else
  exact le_add_right <| hA_card ▸ mem_upperBounds.1 (width_spec (S.erase a)).2 A.card
    ⟨A, by grind, hA_anti, rfl⟩

end PartialOrder
