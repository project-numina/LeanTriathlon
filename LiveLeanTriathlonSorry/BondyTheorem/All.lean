/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib
public import LiveLeanTriathlonSorry.Util.Attributes
@[expose] public section

section Main

open Set Finset

def hypercubeGraph (n : ℕ) : SimpleGraph (Finset (Fin n)) where
  Adj A B := (symmDiff A B).card = 1
  symm A B h := by
    simp only at *
    rw [symmDiff_comm]
    exact h
  loopless := ⟨ by simp ⟩

@[AMS 05]
theorem bondy {n : ℕ} (hn : 0 < n) {A : Fin n → Finset (Fin n)}
    (h_disj : ∀ i j : Fin n, i ≠ j → A i ≠ A j) :
    ∃ S : Finset (Fin n),
      S.card + 1 = n ∧
      ∀ i j : Fin n, i ≠ j → (S) ∩ A i ≠ (S) ∩ A j := by sorry

end Main
