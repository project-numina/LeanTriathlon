/-
Copyright (c) 2026 Krsto Proroković. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krsto Proroković and Numina Team
-/

module
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Attr.Register
public import LiveLeanTriathlonSorry.Util.Attributes
@[expose] public section

section Background

open scoped BigOperators

universe u

namespace Kraft

variable {σ : Type*} [Fintype σ] [DecidableEq σ] [Nonempty σ]

abbrev Code (σ : Type*) := Finset (List σ)

def PrefixFree (C : Code σ) : Prop :=
  ∀ w₁ ∈ C, ∀ w₂ ∈ C, w₁.IsPrefix w₂ → w₁ = w₂

def kraftSum (σ : Type*) [Fintype σ] (ls : List ℕ) : ℚ :=
  (ls.map (fun l => (1 : ℚ) / (Fintype.card σ : ℚ) ^ l)).sum

def stringsOfLength (n : ℕ) :
    Finset (List σ) :=
  Finset.univ.image (fun f : Fin n → σ => List.ofFn f)

def extensions (w : List σ) (n : ℕ) : Finset (List σ) :=
  (stringsOfLength n).filter (fun v => w.IsPrefix v)

def blocked (C : Code σ) (w : List σ) : Prop :=
  (∃ c ∈ C, c.IsPrefix w) ∨ (∃ c ∈ C, w.IsPrefix c)

instance blockedDecidable (C : Code σ) (w : List σ) : Decidable (blocked C w) :=
  inferInstanceAs (Decidable (_ ∨ _))

end Kraft

end Background

section Main

universe u

namespace Kraft

variable {σ : Type u} [Fintype σ] [DecidableEq σ] [Nonempty σ]

@[AMS 68]
theorem kraft (ls : List ℕ) (hkraft : kraftSum σ ls ≤ 1) :
    ∃ C : Code σ, PrefixFree C ∧
      C.val.map List.length = (ls : Multiset ℕ) := by sorry

end Kraft

end Main
