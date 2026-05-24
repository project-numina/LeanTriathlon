/-
Copyright (c) 2026 Krsto Proroković. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krsto Proroković and Numina Team
-/

module
import Mathlib.Tactic.Attr.Register
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import LiveLeanTriathlonSorry.Util.Attributes
@[expose] public section

section Background

open scoped BigOperators

universe u

variable {σ : Type*} [Fintype σ] [Nonempty σ]

abbrev Code (σ : Type*) := Finset (List σ)

def encode (C : Code σ) (ws : List C) : List σ :=
  (ws.map (·.val)).flatten

def UniquelyDecodable (C : Code σ) : Prop :=
  Function.Injective (encode C)

def kraftSum (C : Code σ) : ℚ :=
  ∑ w ∈ C, (1 : ℚ) / ((Fintype.card σ : ℚ) ^ w.length)

def maxLength (C : Code σ) : ℕ :=
  C.sup List.length

def totalLength (C : Code σ) (n : ℕ) (t : Fin n → C) : ℕ :=
  ∑ i, (t i).val.length

def tupleEncode (C : Code σ) (n : ℕ) (t : Fin n → C) : List σ :=
  (List.ofFn (fun i => (t i).val)).flatten

end Background

section Main

universe u

variable {σ : Type u} [Fintype σ] [Nonempty σ]

@[AMS 68]
theorem mcmillan (C : Code σ) (hC : UniquelyDecodable C) :
    kraftSum C ≤ 1 := by sorry

end Main
