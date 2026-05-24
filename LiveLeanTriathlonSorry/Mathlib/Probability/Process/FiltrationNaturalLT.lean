/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä and Numina team
-/
module

public import Mathlib.Probability.Process.Adapted
public import Mathlib.Probability.Process.Filtration

@[expose] public section

open MeasureTheory TopologicalSpace

variable {Ω : Type*}
variable {β : Type*} [TopologicalSpace β] [MetrizableSpace β] [mβ : MeasurableSpace β] [BorelSpace β]
variable {ι : Type*} [Preorder ι]

def Filtration.naturalLT
    {m : MeasurableSpace Ω} (u : ι → Ω → β) (hum : ∀ i, StronglyMeasurable[m] (u i)) :
    Filtration ι m where
  seq i := ⨆ j < i, MeasurableSpace.comap (u j) mβ
  mono' i j hij := by
    exact biSup_mono fun k hki ↦ hki.trans_le hij
  le' i := by
    refine iSup₂_le ?_
    rintro j hji s ⟨t, ht, rfl⟩
    exact (hum j).measurable ht

lemma Filtration.naturalLT_mono
    {m : MeasurableSpace Ω} (u : ι → Ω → β) (hum : ∀ i, StronglyMeasurable[m] (u i)) :
    Monotone (Filtration.naturalLT u hum) :=
  fun _ _ hij ↦ Filtration.mono _ hij

lemma Filtration.naturalLT_le_natural
    {m : MeasurableSpace Ω} (u : ι → Ω → β) (hum : ∀ i, StronglyMeasurable[m] (u i)) :
    (Filtration.naturalLT (m := m) u hum) ≤ (Filtration.natural (m := m) u hum) := by
  apply fun i ↦ biSup_mono fun j hji ↦ hji.le

lemma Filtration.measurable_naturalLT
    {m : MeasurableSpace Ω} (u : ι → Ω → β) (hum : ∀ i, StronglyMeasurable (u i))
    {i j : ι} (hij : i < j) :
    Measurable[Filtration.naturalLT u hum j] (u i) :=
  Measurable.of_comap_le <| le_iSup₂_of_le i hij fun _ mble ↦ mble

lemma Filtration.naturalLT_apply_le_of_forall_measurable [SecondCountableTopology β]
    {m : MeasurableSpace Ω} (u : ι → Ω → β) (hum : ∀ i, Measurable[m] (u i)) (i : ι) :
    Filtration.naturalLT (m := m) u (fun j ↦ (hum j).stronglyMeasurable) i ≤ m := by
  simpa [naturalLT, iSup_le_iff] using fun j _ ↦ measurable_iff_comap_le.mp (hum j)

lemma Filtration.adapted_naturalLT_nat {α : Type*} {β : Type*}
    [MeasurableSpace α] [TopologicalSpace α] [TopologicalSpace.MetrizableSpace α]
    [SecondCountableTopology α] [BorelSpace α]
    [MeasurableSpace β] [TopologicalSpace β] [TopologicalSpace.MetrizableSpace β]
    [SecondCountableTopology β] [OpensMeasurableSpace β]
    {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → α} (X_mble : ∀ n, Measurable (X n))
    (fs : Π (n : ℕ), (Fin n → α) → β) (fs_mble : ∀ n, Measurable (fs n)) :
    StronglyAdapted (m := ‹MeasurableSpace Ω›)
      (Filtration.naturalLT (m := ‹MeasurableSpace Ω›) X (by measurability))
      (fun (n : ℕ) ω ↦ (fs n) (fun (i : Fin n) ↦ X i ω)) := by
  intro n
  apply Measurable.stronglyMeasurable
  apply (fs_mble n).comp
  apply (@measurable_pi_iff Ω (Fin n) (fun _ ↦ α)
         (Filtration.naturalLT X (by measurability) n) _).mpr
  exact fun i ↦ Filtration.measurable_naturalLT _ _ i.isLt

lemma Filtration.adapted_naturalLT_nat' {α : Type*} {β : Type*}
    [MeasurableSpace α] [TopologicalSpace α] [TopologicalSpace.MetrizableSpace α]
    [SecondCountableTopology α] [BorelSpace α]
    [MeasurableSpace β] [TopologicalSpace β] [TopologicalSpace.MetrizableSpace β]
    [SecondCountableTopology β] [OpensMeasurableSpace β]
    {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → α} (X_mble : ∀ n, Measurable (X n))
    (fs : Π (n : ℕ), (Finset.range n → α) → β) (fs_mble : ∀ n, Measurable (fs n)) :
    StronglyAdapted (m := ‹MeasurableSpace Ω›)
      (Filtration.naturalLT (m := ‹MeasurableSpace Ω›) X (by measurability))
      (fun (n : ℕ) ω ↦ (fs n) (fun (i : Finset.range n) ↦ X i ω)) := by
  intro n
  apply Measurable.stronglyMeasurable
  apply (fs_mble n).comp
  apply (@measurable_pi_iff Ω (Finset.range n) (fun _ ↦ α)
         (Filtration.naturalLT X (by measurability) n) _).mpr
  exact fun i ↦ Filtration.measurable_naturalLT _ _ (show i < n by aesop)
