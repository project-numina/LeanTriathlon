/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib.Order.Antichain
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Data.Int.Star
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Tactic.Attr.Register
public import LiveLeanTriathlonSorry.Util.Attributes
public import LiveLeanTriathlonSorry.Mathlib.Order.Antichain.Width
public import LiveLeanTriathlonSorry.Mathlib.Classical.Choose
@[expose] public section

section Background

open Finset Nat

universe u

variable {P : Type u}

namespace PartialOrder

variable [PartialOrder P]

def IsChainPartition (C : Set (Set P)) (S : Set P) : Prop :=
  (∀ c ∈ C, c ≠ ∅)
  ∧
  (∀ c ∈ C, IsChain (· ≤ ·) c)
  ∧
  (∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → Disjoint c₁ c₂)
  ∧
  (C.sUnion = S)

-- Needed for def

lemma inter_unique {S' : Finset P} {C : Finset (Set P)} {k : ℕ} (hC_partition : IsChainPartition (SetLike.coe C) (SetLike.coe S'))
    (hC_card : C.card = k) (A' : Finset P) (hA'_sub : A' ⊆ S') (hA'_anti : IsAntichain (· ≤ ·) (SetLike.coe A'))
    (hA'_card : A'.card = k) (c : Set P) (hc : c ∈ C) :
    ∃! a' ∈ A', a' ∈ c := by sorry

-- Needed for def

lemma inter_unique' {S' : Finset P} {C : Finset (Set P)} (hC_partition : IsChainPartition (SetLike.coe C) (SetLike.coe S'))
     (A' : Finset P) (hA'_sub : A' ⊆ S') (hA'_anti : IsAntichain (· ≤ ·) (SetLike.coe A'))
    (hA'_card : A'.card = C.card ) (c : Set P) (hc : c ∈ C) :
    ∃! a' ∈ A', a' ∈ c := sorry

noncomputable def unique_antichain_element {S' : Finset P} {C : Finset (Set P)} {k : ℕ}
    (hC_partition : IsChainPartition (SetLike.coe C) (SetLike.coe S')) (hC_card : C.card = k)
    (A' : Finset P) (hA'_sub : A' ⊆ S') (hA'_anti : IsAntichain (· ≤ ·) (SetLike.coe A'))
    (hA'_card : A'.card = k) (c : Set P) (hc : c ∈ C) : P :=
  (inter_unique hC_partition hC_card A' hA'_sub hA'_anti hA'_card c hc).choose

-- Needed for def

lemma unique_antichain_element_mem_antichain {S' : Finset P} {C : Finset (Set P)} {k : ℕ}
    (hC_partition : IsChainPartition (SetLike.coe C) (SetLike.coe S')) (hC_card : C.card = k)
    (A' : Finset P) (hA'_sub : A' ⊆ S') (hA'_anti : IsAntichain (· ≤ ·) (SetLike.coe A'))
    (hA'_card : A'.card = k) (c : Set P) (hc : c ∈ C) :
    unique_antichain_element hC_partition hC_card A' hA'_sub hA'_anti hA'_card c hc ∈ A' := sorry

-- Needed for def

lemma unique_antichain_element_mem_chain {S' : Finset P} {C : Finset (Set P)} {k : ℕ}
    (hC_partition : IsChainPartition (SetLike.coe C) (SetLike.coe S')) (hC_card : C.card = k)
    (A' : Finset P) (hA'_sub : A' ⊆ S') (hA'_anti : IsAntichain (· ≤ ·) (SetLike.coe A'))
    (hA'_card : A'.card = k) (c : Set P) (hc : c ∈ C) :
    unique_antichain_element hC_partition hC_card A' hA'_sub hA'_anti hA'_card c hc ∈ c := sorry

def fullAntichains (C : Finset (Set P)) (S : Finset P) : Set (Finset P) :=
  { A | IsAntichain (· ≤ ·) (SetLike.coe A) ∧ A ⊆ S ∧ A.card = C.card }

-- Needed for def

lemma subset_of_mem_fullAntichains {C : Finset (Set P)} {S : Finset P} {A : Finset P}
    (hA : A ∈ fullAntichains C S) : A ⊆ S := sorry

-- Needed for def

lemma antichain_of_mem_fullAntichains {C : Finset (Set P)} {S : Finset P} {A : Finset P}
    (hA : A ∈ fullAntichains C S) : IsAntichain (· ≤ ·) (SetLike.coe A) := sorry

lemma card_of_mem_fullAntichains {C : Finset (Set P)} {S : Finset P} {A : Finset P}
    (hA : A ∈ fullAntichains C S) : A.card = C.card := sorry

variable [Fintype P]

open scoped Classical in
@[simp]
noncomputable def fullChainMaximizers (C : Finset (Set P)) (S : Finset P)
  (h_is_chain_partition : IsChainPartition (SetLike.coe C) (SetLike.coe S)) : Finset P :=
  if
    ne : fullAntichains C S = ∅
  then ∅
  else
      {x | ∃ c, ∃ hcC : c ∈ C, x = Classical.choose
        (p := Maximal (fun y => y ∈ ({x | x ∈ c ∧ ∃ Ai ∈ fullAntichains C S, x ∈ Ai}.toFinset)))
        (by
          apply Finset.exists_maximal
          push Not at ne
          obtain ⟨A, hA⟩ := ne
          use unique_antichain_element h_is_chain_partition rfl A
                (subset_of_mem_fullAntichains hA) (antichain_of_mem_fullAntichains hA)
                hA.2.2 c (hcC)
          simp only [Set.toFinset_setOf, mem_filter, mem_univ, true_and]
          rw [and_comm]
          constructor
          .
            use A, by simp [hA]
            exact
              unique_antichain_element_mem_antichain h_is_chain_partition (Eq.refl #C) A
                (subset_of_mem_fullAntichains hA) (antichain_of_mem_fullAntichains hA)
                hA.right.right c hcC
          .
            exact
              unique_antichain_element_mem_chain h_is_chain_partition (Eq.refl #C) A
                (subset_of_mem_fullAntichains hA) (antichain_of_mem_fullAntichains hA)
                hA.right.right c hcC ) }.toFinset

end PartialOrder

end Background

section Main

open Finset Nat

universe u

variable {P : Type u}

namespace PartialOrder

variable [PartialOrder P] [Fintype P]

@[AMS 05]
theorem dilworth (S : Finset P) :
    IsLeast {k | ∃ (C : Finset (Set P)), IsChainPartition (SetLike.coe C) S ∧
      C.card = k} (width S) := by sorry

end PartialOrder

end Main
