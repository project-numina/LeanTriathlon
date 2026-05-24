/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Mathlib.NumberTheory.FactorisationProperties
public import Mathlib.Tactic.IntervalCases

@[expose] public section

open Nat

lemma Abundant.pos {n : ℕ} (hn : Abundant n) : 0 < n := by
  rw [Abundant] at hn
  contrapose! hn
  interval_cases n
  simp [properDivisors]

lemma Weird.pos {n : ℕ} (hn : Weird n) : 0 < n := by
  rw [Weird] at hn
  obtain ⟨hn_abundant, hn_not_semiperfect⟩ := hn
  exact Abundant.pos hn_abundant
