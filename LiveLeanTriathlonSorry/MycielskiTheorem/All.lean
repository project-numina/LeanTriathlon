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

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

def mycielskian : SimpleGraph (V ⊕ V ⊕ Unit) where
  Adj x y := match x, y with
    | .inl vi,        .inl vj        => G.Adj vi vj
    | .inl vi,        .inr (.inl uj) => G.Adj vi uj
    | .inr (.inl ui), .inl vj        => G.Adj ui vj
    | .inr (.inl _),  .inr (.inr _)  => True
    | .inr (.inr _),  .inr (.inl _)  => True
    | _,              _              => False
  symm := by
    intro x y h
    rcases x with vi | ui | ⟨⟩ <;> rcases y with vj | uj | ⟨⟩ <;>
      first | exact G.symm h | exact h
  loopless := ⟨fun x h => by
    rcases x with v | u | ⟨⟩
    .
      exact G.loopless.irrefl v h
    .
      exact h
    .
      exact h⟩

@[AMS 05]
theorem mycielski (n : ℕ) :
    ∃ (W : Type) (H : SimpleGraph W), H.CliqueFree 3 ∧ (n : ℕ∞) ≤ H.chromaticNumber := by sorry

end SimpleGraph

end Main
