/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib
public import Mathlib.Analysis.Convex.DoublyStochasticMatrix
public import LiveLeanTriathlonSorry.Util.Attributes
@[expose] public section

section Background

open Matrix Filter Topology

abbrev RVec (N : ℕ) := Fin N → ℝ

abbrev RSMatrix (N : ℕ) := Matrix (Fin N) (Fin N) ℝ

variable {N : ℕ}

noncomputable def RCseq (A : RSMatrix N) (n : ℕ) : (RVec N × RVec N) :=
  match n with
  | 0 => (1, (1 ᵥ* A)⁻¹)
  | n + 1 =>
    let (d, e) := RCseq A n;
    let A' := (diagonal d) * A * (diagonal e);
    let d' := (A' *ᵥ 1)⁻¹;
    let e' := (1 ᵥ* ((diagonal d') * A'))⁻¹;
    (d' * d, e * e')

noncomputable def RCseqLeft (A : RSMatrix N) (n : ℕ) : RVec N := (RCseq A n).1

noncomputable def RCseqRight (A : RSMatrix N) (n : ℕ) : RVec N := (RCseq A n).2

noncomputable def colOneSeq (A : RSMatrix N) (n : ℕ) : RSMatrix N :=
  (diagonal (RCseqLeft A n)) * A * (diagonal (RCseqRight A n))

noncomputable def rowOneSeq (A : RSMatrix N) (n : ℕ) : RSMatrix N :=
  (diagonal (RCseqLeft A (n + 1))) * A * (diagonal (RCseqRight A n))

noncomputable def rowSums (A : RSMatrix N) (n : ℕ) : RVec N := colOneSeq A n *ᵥ 1

noncomputable def colSums (A : RSMatrix N) (n : ℕ) : RVec N := 1 ᵥ* rowOneSeq A n

end Background

section Main

open Matrix Finset Filter Topology

@[AMS 15]
theorem sinkhorn_uniqueness {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 < A i j)
    (d₁ d₂ d₁' d₂' : Fin n → ℝ)
    (hd₁ : ∀ i, 0 < d₁ i)
    (hd₂ : ∀ i, 0 < d₂ i)
    (hd₁' : ∀ i, 0 < d₁' i)
    (hd₂' : ∀ i, 0 < d₂' i)
    (hDS : diagonal d₁ * A * diagonal d₂ ∈ doublyStochastic ℝ (Fin n))
    (hDS' : diagonal d₁' * A * diagonal d₂' ∈ doublyStochastic ℝ (Fin n)) :
    ∃ c : ℝ, 0 < c ∧
      (∀ i, d₁' i = c * d₁ i) ∧
      (∀ i, d₂' i = d₂ i / c) := by sorry

end Main
