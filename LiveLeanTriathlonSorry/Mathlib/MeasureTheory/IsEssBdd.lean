/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

@[expose] public section

open ENNReal MeasureTheory Pointwise Real Set Filter MeasurableSet

abbrev IsEssBdd {α β : Type*} [MeasurableSpace α] [ConditionallyCompleteLattice β] (f : α → β)
    (μ : Measure α := by volume_tac) := IsBoundedUnder (fun (x1 x2 : β) ↦ x1 ≤ x2) (ae μ) f

lemma nonneg_essSup_of_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α} [hμ_neZero : NeZero μ]
    {f : α → ℝ} (hf_nonneg : 0 ≤ f) : 0 ≤ essSup f μ := essSup_eq_sInf μ f ▸ Real.sInf_nonneg
  fun y hy ↦ by_contra fun hy_neg ↦ by
  have : 0 < μ {x | y < f x} := lt_of_lt_of_eq (Measure.measure_univ_pos.mpr hμ_neZero.ne)
    congr(μ $((Set.eq_univ_of_forall fun x ↦ lt_of_lt_of_le (not_le.1 hy_neg) (hf_nonneg x)).symm))
  grind

noncomputable def superlevel_set {α β : Type*} [LT β] (f : α → β) (c : β) : Set α := {x | c < f x}

lemma ae_zero_of_nonneg_essSup_zero_essBdd {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf_nonneg : 0 ≤ f) (hf_essBdd : IsEssBdd f μ) (hf_essSup_zero : essSup f μ = 0) :
    f =ᵐ[μ] 0 := (by simpa [EventuallyLE, ← hf_essSup_zero] using ae_le_essSup hf_essBdd :
  f ≤ᵐ[μ] 0).antisymm <| Eventually.of_forall hf_nonneg

lemma le_of_forall_le_of_lt {a b : ℝ} (h : ∀ c, c < a → c ≤ b) : a ≤ b := by_contra fun hba ↦ by
  obtain ⟨c, hac, hcb⟩ := exists_between <| by simpa using hba
  exact not_lt_of_ge (h c hcb) hac

lemma extract_bddbelow {α β : Type*} {f : α → β} [MeasurableSpace α] (μ : Measure α := by volume_tac)
    [ConditionallyCompleteLinearOrder β]  [NeZero μ] {a : β} (ha : ∀ (x : α), a ≤ f x) :
    BddBelow {y | μ {x | y < f x} = 0} := ⟨a, fun y ↦ not_imp_not.1 fun hy ↦ by
    simp_all [show {x | y < f x} = univ from eq_univ_of_forall fun _ ↦ lt_of_lt_of_le (not_le.1 hy)
      (ha _), ← neZero_iff]⟩

lemma div_essSup_of_essBdd_lowerBdd {α : Type*} [MeasurableSpace α] (μ : Measure α := by volume_tac)
    [NeZero μ] {f : α → ℝ} (hf_essBdd : IsEssBdd f μ) {a : ℝ} (ha_le_f : ∀ (x : α), a ≤ f x) {b : ℝ}
    (hb_pos : 0 < b) : essSup (fun x ↦ (f x) / b) μ = (essSup f μ) / b := essSup_eq_sInf μ f ▸
  essSup_eq_sInf μ (fun x ↦ (f x) / b) ▸
  have h1 : BddBelow {d | μ {x | d < f x / b} = 0} := extract_bddbelow (f := fun x ↦ (f x) / b) μ
    (a := a / b) (fun x ↦ by simpa using by gcongr; exact ha_le_f x)
  have h2 : BddBelow {d | μ {x | d < f x} = 0} := extract_bddbelow _ ha_le_f
  le_antisymm (le_of_forall_le_of_lt fun c hc ↦ le_div_iff₀ hb_pos|>.2 <| le_csInf
  ⟨essSup f μ, by simpa using meas_essSup_lt⟩ fun d hd ↦ by_contra fun hdcb ↦ (ne_of_lt <|
  lt_of_lt_of_le (lt_of_le_of_ne (by simp) (Ne.symm <| by simpa using notMem_of_lt_csInf hc h1)) <|
  measure_mono fun e he ↦ (not_le.1 hdcb).trans <| (lt_div_iff₀ hb_pos).1 he) hd.symm) <|
  le_of_forall_le_of_lt fun c hc ↦ le_csInf ⟨(essSup f μ) / b, by
  simpa [div_lt_div_iff_of_pos_right hb_pos] using meas_essSup_lt⟩ <| fun d hd ↦ by_contra fun hdc ↦
  (ne_of_lt <| lt_of_lt_of_le (lt_of_le_of_ne (by simp) (Ne.symm <| by simpa using (notMem_of_lt_csInf
  (lt_div_iff₀ hb_pos|>.1 hc) h2))) <| measure_mono <| by
  simpa [lt_div_iff₀ hb_pos] using fun a ha ↦ lt_trans (by gcongr; exact not_le.1 hdc) ha) hd.symm

lemma nonempty_of_superlevel_set_of_bddBelow {α β : Type*} [MeasurableSpace α]
    [ConditionallyCompleteLinearOrder β] (μ : Measure α := by volume_tac) [NeZero μ]
    {f : α → β} {a : β} (ha : ∀ (x : α), a ≤ f x) {b : β} (hb : b < essSup f μ) :
    (superlevel_set f b).Nonempty := nonempty_of_measure_ne_zero (μ := μ) <| by
  simpa using notMem_of_lt_csInf (essSup_eq_sInf μ f ▸ hb) <| extract_bddbelow μ ha

lemma lintegral_eq_lintegral_meas_superlevelset
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α := by volume_tac)
    {f : α → ℝ} (hf_nonneg : 0 ≤ f) (hf_integrable : Integrable f μ) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ
      = ∫⁻ t, indicator (Ioi 0) (fun y ↦ (μ (superlevel_set f y))) t ∂volume := by
  rw [lintegral_indicator measurableSet_Ioi]
  exact lintegral_eq_lintegral_meas_lt μ
    (ae_of_all _ (fun _ ↦ hf_nonneg _))
    (Integrable.aemeasurable hf_integrable)

lemma Ioo_disjoint_Ici_same {α : Type*} [LinearOrder α] {a b : α} : Disjoint (Ioo a b) (Ici b) := by
  grind

lemma fin_vol_of_superlevelset_of_nonneg_integrable
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} (hf_nonneg : 0 ≤ f) {c : ℝ}
    (hf_integrable : Integrable f μ) (hc_pos : 0 < c) : μ (superlevel_set f c) < ⊤ := by
  have g_le_f_ennreal : indicator (superlevel_set f c) (Function.const _ (ENNReal.ofReal c)) ≤
      .ofReal ∘ f := fun x ↦ by
    rcases @or_not (x ∈ superlevel_set f c) with ha_mem_s | ha_not_mem_s
    · simpa [indicator_of_mem ha_mem_s, ENNReal.ofReal_le_ofReal_iff (hf_nonneg x)] using le_of_lt ha_mem_s
    · simp [indicator_of_notMem ha_not_mem_s]
  refine ENNReal.lt_top_of_mul_ne_top_right (ne_of_lt ?_)
    (pos_iff_ne_zero.mp (ENNReal.ofReal_pos.mpr hc_pos))
  erw [← lintegral_indicator_const₀ (nullMeasurableSet_lt aemeasurable_const
    (Integrable.aemeasurable hf_integrable))]
  exact lt_of_le_of_lt (lintegral_mono g_le_f_ennreal) <| (hasFiniteIntegral_iff_ofReal <|
    ae_of_all _ hf_nonneg).1 (Integrable.hasFiniteIntegral hf_integrable)

lemma essSup_eq_one {f : EuclideanSpace ℝ (Fin 1) → ℝ} (hf1 : 0 ≤ f)
    (hf3 : IsEssBdd f volume) (hf4 : 0 < essSup f volume) :
    essSup (fun x ↦ f x / essSup f volume) volume = 1 := by
  simpa [← div_self (ne_of_gt hf4)] using div_essSup_of_essBdd_lowerBdd _ hf3 hf1 hf4
