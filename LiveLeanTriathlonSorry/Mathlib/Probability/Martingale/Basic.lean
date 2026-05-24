/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä and Numina team
-/
module

public import LiveLeanTriathlonSorry.Mathlib.Probability.Process.FiltrationNaturalLT
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Martingale.Basic
import Mathlib.Tactic.Attr.Register

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma sum_terms_mgale' {X : ℕ → Ω → ℝ} (X_mble : ∀ n, Measurable (X n))
    (X_intble : ∀ n, Integrable (X n) P) (X_zeromean : ∀ n, ∫ ω, X n ω ∂P = 0)
    (X_indep : iIndepFun X P) :
    Martingale (m0 := ‹MeasurableSpace Ω›) (fun n ↦ ∑ (i : Fin n), X i)
               (Filtration.naturalLT (m := ‹MeasurableSpace Ω›) X (by measurability)) P := by
  refine martingale_nat ?_ ?_ ?_
  · convert @Filtration.adapted_naturalLT_nat ℝ ℝ _ _ _ _ _ _ _ _ _ _ Ω _ X X_mble
            (fun n ts ↦ ∑ (i : Fin n), ts i) ?_
    · simp
    · measurability
  · exact fun i ↦ integrable_finset_sum' Finset.univ fun j a ↦ X_intble j
  · intro n
    simp only [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    simp only [dite_eq_ite, lt_add_iff_pos_right, zero_lt_one, ↓reduceDIte]
    have aux {k} (hk : n ≤ k) :
        (∑ i ∈ Finset.range n, if i < k then X i else 0) = (∑ i ∈ Finset.range n, X i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_range] at hi
      simp [hi.trans_le hk]
    simp only [aux le_rfl, aux (show n ≤ n+1 by linarith)]
    apply ae_eq_trans _ (condExp_add ?_ ?_ _).symm
    · have key : P[X n|(Filtration.naturalLT (m := ‹MeasurableSpace Ω›) X (by measurability) n)]
                  =ᶠ[ae P] fun _ ↦ ∫ (ω : Ω), X n ω ∂P := by
        have := Filtration.naturalLT_apply_le_of_forall_measurable (m := ‹MeasurableSpace Ω›) X X_mble
        refine condExp_indep_eq (m₁ :=MeasurableSpace.comap (X n) inferInstance)
                (m₂ := Filtration.naturalLT (m := ‹MeasurableSpace Ω›) X (by measurability) n)
                (μ := P) ?_ ?_ ?_ ?_
        · exact measurable_iff_comap_le.mp (X_mble n)
        · exact (Measurable.of_comap_le fun _ mble ↦ mble).stronglyMeasurable
        · simpa using indep_iSup_of_disjoint
                        (fun i ↦ measurable_iff_comap_le.mp (X_mble i)) X_indep
                        (S := {n}) (T := Set.Iio n) (by aesop)
      rw [condExp_of_stronglyMeasurable]
      · rw [← add_zero (∑ i ∈ Finset.range n, X i)]
        refine EventuallyEq.add (by simp) ?_
        apply ae_eq_trans _ key.symm
        simp_all only
        rfl
      · apply Finset.stronglyMeasurable_sum
        intro i hi
        have hi' : i < n := by simpa only [Finset.mem_range] using hi
        apply StronglyMeasurable.mono
              (Filtration.measurable_naturalLT X (by measurability) hi').stronglyMeasurable _
        rfl
      · exact integrable_finset_sum' (Finset.range n) fun i _ ↦ X_intble i
    · exact integrable_finset_sum' _ fun i _ ↦ X_intble i
    · exact X_intble n

lemma sum_terms_mgale {X : ℕ → Ω → ℝ} (X_mble : ∀ n, Measurable (X n))
    (X_intble : ∀ n, Integrable (X n) P) (X_zeromean : ∀ n, ∫ ω, X n ω ∂P = 0)
    (X_indep : iIndepFun X P) :
    Martingale (m0 := ‹MeasurableSpace Ω›) (fun n ↦ ∑ i ∈ Finset.range n, X i)
               (Filtration.naturalLT X (by measurability) ) P := by
  convert sum_terms_mgale' X_mble X_intble X_zeromean X_indep
  exact Finset.sum_range X
