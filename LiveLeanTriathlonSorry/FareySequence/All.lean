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

open Rat Set Filter

def FareySet (k : ℕ) : Finset ℚ :=
  (Finset.range (k + 1)).biUnion
    (fun d => (((Finset.range (d+1)).image fun (n : ℕ) => (n : ℚ) / (d : ℚ))))

def FareyCard (k : ℕ) : ℕ :=
  (FareySet k).card

def FareySequence (k : ℕ) (i : Fin (FareyCard k)) : ℚ :=
  ((FareySet k).sort (fun x y => x ≤ y)).getD i 0

def FareyDifference (k : ℕ) (i : Fin (FareyCard k)) : ℚ :=
  let m := FareyCard k
  let f := FareySequence k i
  f - (i / (m - 1))

@[AMS 11]
theorem farey_riemann_abs :
    RiemannHypothesis ↔ ∀ r : ℝ,
      1 / 2 < r → (fun n ↦ ∑' i : Fin (FareyCard n), |FareyDifference n i|)
        =O[atTop] (fun n ↦ (↑n : ℝ) ^ r) := by sorry

end Main
