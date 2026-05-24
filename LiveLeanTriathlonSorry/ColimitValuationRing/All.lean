/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Algebra.Colimit.Ring
public import LiveLeanTriathlonSorry.Util.Attributes
@[expose] public section

section Background

open Ring

universe u v

variable {ι : Type v} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]

variable {G : ι → Type u} [∀ i, CommRing (G i)]

variable (f : ∀ i j, i ≤ j → G i →+* G j)

variable [DirectedSystem G (fun i j h => f i j h)]

-- Needed for def

lemma Ring.DirectLimit.nontrivial_of_nontrivial [∀ i, Nontrivial (G i)] :
    Nontrivial (Ring.DirectLimit G (fun i j h => f i j h)) := by sorry

-- Needed for def

lemma Ring.DirectLimit.noZeroDivisors_of_isDomain [∀ i, IsDomain (G i)] :
    NoZeroDivisors (Ring.DirectLimit G (fun i j h => f i j h)) := by sorry

instance Ring.DirectLimit.isDomain_of_isDomain [∀ i, IsDomain (G i)] :
    IsDomain (Ring.DirectLimit G (fun i j h => f i j h)) := by
  have := Ring.DirectLimit.nontrivial_of_nontrivial f
  have := Ring.DirectLimit.noZeroDivisors_of_isDomain f
  exact NoZeroDivisors.to_isDomain _

end Background

section Main

open Ring

universe u v

variable {ι : Type v} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]

variable {G : ι → Type u} [∀ i, CommRing (G i)]

variable (f : ∀ i j, i ≤ j → G i →+* G j)

variable [DirectedSystem G (fun i j h => f i j h)]

-- Needed for def

omit [DirectedSystem G fun i j h ↦ ⇑(f i j h)] in
lemma Ring.DirectLimit.dvd_total
    [∀ i, IsDomain (G i)] [∀ i, ValuationRing (G i)]
    (a b : Ring.DirectLimit G (fun i j h => f i j h)) :
    a ∣ b ∨ b ∣ a := by sorry

@[stacks 0AS4, AMS 13]
instance Ring.DirectLimit.instValuationRing
    [∀ i, IsDomain (G i)] [∀ i, ValuationRing (G i)] :
    ValuationRing (Ring.DirectLimit G (fun i j h => f i j h)) :=
  ValuationRing.iff_dvd_total.mpr ⟨Ring.DirectLimit.dvd_total f⟩

end Main
