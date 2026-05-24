/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä and Numina team
-/
module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Tactic
public import LiveLeanTriathlonSorry.Mathlib.Analysis.SpecialFunctions.Pow.NNReal

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma evariance_eq_eLpNorm_two_sq_of_mean_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : Ω → ℝ} (Z_zeromean : ∫ ω, Z ω ∂P = 0) :
    eVar[Z; P] = (eLpNorm Z 2 P)^2 := by

  simp [evariance, eLpNorm, eLpNorm', Z_zeromean]

lemma eLpNorm_two_eq_evariance_pow_half_of_mean_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : Ω → ℝ} (Z_zeromean : ∫ ω, Z ω ∂P = 0) :
    (eLpNorm Z 2 P) = (eVar[Z; P]) ^ (2⁻¹ : ℝ) := by
  apply ENNReal.injective_sq
  simp [evariance_eq_eLpNorm_two_sq_of_mean_zero Z_zeromean]

variable [IsProbabilityMeasure P]

lemma ProbabilityTheory.variance_truncated_le {Z : Ω → ℝ}
    (Z_mble : AEStronglyMeasurable Z P) (Z_sqint : MemLp Z 2 P) {A : Set Ω}
    (A_mble : NullMeasurableSet A P) :
    Var[Set.indicator A Z; P] ≤ ∫ ω, Z ω^2 ∂P := by
  let A' := toMeasurable P A
  have hA' : MeasurableSet A' := measurableSet_toMeasurable P A
  have ind_memLp : MemLp (Set.indicator A' Z) 2 P := Z_sqint.indicator hA'
  have ind_eq : Set.indicator A Z =ᵐ[P] Set.indicator A' Z := by
    have obs₁ : A ⊆ A' := subset_toMeasurable (μ := P) A
    have obs₂ : P A' = P A := measure_toMeasurable (μ := P) A
    have filt : (A' \ A)ᶜ ∈ ae P := by
      simp only [ae, mem_ofCountableUnion, compl_compl]
      rw [measure_diff obs₁, obs₂, tsub_self]
      · exact A_mble
      · exact measure_ne_top P A
    filter_upwards [filt] with ω hω
    simp only [Set.mem_compl_iff, Set.mem_diff, not_and, not_not] at hω
    by_cases h : ω ∈ A'
    · simp [h, hω h]
    · simp [h, show ω ∉ A from fun con ↦ h (obs₁ con)]
  calc Var[Set.indicator A Z; P]
      = Var[Set.indicator A' Z; P] := variance_congr ind_eq
    _ = ∫ ω, (Set.indicator A' Z ω) ^ 2 ∂P - (∫ ω, Set.indicator A' Z ω ∂P) ^ 2 :=
        variance_eq_sub ind_memLp
    _ ≤ ∫ ω, (Set.indicator A' Z ω) ^ 2 ∂P := by
        linarith [show (∫ ω, Set.indicator A' Z ω ∂P) ^ 2 ≥ 0 from sq_nonneg _]
    _ ≤ ∫ ω, Z ω ^ 2 ∂P := by
        have intble : Integrable (fun ω ↦ (Set.indicator A' Z ω) ^ 2) P := by
          simpa [memLp_two_iff_integrable_sq (Z_mble.indicator hA')] using ind_memLp
        refine integral_mono intble ((memLp_two_iff_integrable_sq Z_mble).mp Z_sqint) ?_
        intro ω
        by_cases h : ω ∈ A'
        · simp [h]
        · simp [h, sq_nonneg]

lemma MeasureTheory.lintegral_pow_eq_top_of_not_memLp
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {Z : α → ℝ} (Z_mble : AEStronglyMeasurable Z μ) (hZ : ¬ MemLp Z 2 μ) :
    ∫⁻ a, ENNReal.ofReal |Z a|^2 ∂μ = ∞ := by
  simp only [MemLp, not_and, not_lt, top_le_iff] at hZ
  specialize hZ Z_mble
  simp only [eLpNorm, OfNat.ofNat_ne_zero, ↓reduceIte, ENNReal.ofNat_ne_top, eLpNorm',
             ENNReal.toReal_ofNat, ENNReal.rpow_ofNat, one_div, ENNReal.rpow_eq_top_iff,
             inv_neg'', (show ¬(2 : ℝ) < 0 by linarith), and_false, inv_pos, Nat.ofNat_pos,
             and_true, false_or] at hZ
  rw [← hZ]
  congr
  funext ω
  congr
  simpa only [enorm, nnnorm, Real.norm_eq_abs] using ENNReal.ofReal_eq_coe_nnreal ..

omit [IsProbabilityMeasure P] in
lemma ProbabilityTheory.tendsto_lintegral_truncated_pow_atTop_of_not_memLp
    {Z : Ω → ℝ} (Z_mble : Measurable Z) (hZ : ¬ MemLp Z 2 P) :
    Tendsto (fun b ↦ ∫⁻ ω, ENNReal.ofReal (Set.indicator {ω | |Z ω| ≤ b} |Z| ω)^2 ∂P)
        atTop (𝓝 ∞) := by
  have normsq_Z_infty : ∫⁻ ω, ENNReal.ofReal |Z ω|^2 ∂P = ∞ :=
    MeasureTheory.lintegral_pow_eq_top_of_not_memLp Z_mble.aestronglyMeasurable hZ
  suffices ∀ (bs : ℕ → ℝ) (_ : Monotone bs) (_ : Tendsto bs atTop atTop),
      Tendsto (fun n ↦ ∫⁻ ω, ENNReal.ofReal (Set.indicator {ω | |Z ω| ≤ bs n} |Z| ω)^2 ∂P)
        atTop (𝓝 ∞) by
    have key := this Nat.cast (fun _ _ h ↦ Nat.cast_le.mpr h) tendsto_natCast_atTop_atTop
    have integrand_mono : Monotone fun b ↦
        (∫⁻ ω, ENNReal.ofReal (Set.indicator {ω | |Z ω| ≤ b} |Z| ω)^2 ∂P) := by
      intro b₁ b₂ hb
      apply lintegral_mono
      intro ω
      by_cases hZω : |Z ω| ≤ b₁
      · simp [hZω, hZω.trans hb]
      · simp [hZω]
    rw [ENNReal.tendsto_nhds_top_iff_nnreal] at *
    intro x
    obtain ⟨n, hn⟩ := (key x).exists
    rw [eventually_atTop]
    exact ⟨Nat.cast n, fun b hb ↦ lt_of_lt_of_le hn (integrand_mono hb)⟩
  intro bs bs_mono hbs
  rw [← normsq_Z_infty]
  have Zbabs_mble (b) : Measurable (fun x ↦ ({ω | |Z ω| ≤ b}.indicator |Z| x)) := by
    apply Measurable.indicator (Measurable.norm Z_mble)
    refine measurableSet_le (Measurable.norm Z_mble) measurable_const
  have Zb_sq_mble (b) : Measurable (fun x ↦ ENNReal.ofReal ({ω | |Z ω| ≤ b}.indicator |Z| x) ^ 2) := by
    have aux : Measurable (fun (y : ℝ≥0∞) ↦ (⟨y, 2⟩ : ℝ≥0∞ × ℕ)) := by measurability
    apply (measurable_pow.comp aux).comp
    simp only [ENNReal.some_eq_coe, measurable_coe_nnreal_ennreal_iff]
    refine Measurable.real_toNNReal (Zbabs_mble b)
  apply lintegral_tendsto_of_tendsto_of_monotone
  · exact fun n ↦ (Zb_sq_mble (bs n)).aemeasurable
  · apply Eventually.of_forall
    intro ω n m hnm
    by_cases hZω : |Z ω| ≤ bs n
    · simp [hZω, hZω.trans (bs_mono hnm)]
    · simp [hZω]
  · apply Eventually.of_forall
    intro ω
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [hbs (Ici_mem_atTop (|Z ω|))] with n hn using by aesop

lemma ProbabilityTheory.IndepFun.memLp_of_memLp_add {Z W : Ω → ℝ}
    (Z_mble : Measurable Z) (W_mble : Measurable W)
    (ZW_indep : IndepFun Z W P) (add_mem_L2 : MemLp (Z + W) 2 P ) :
    MemLp Z 2 P := by
  have normsq_add_finite : ∫⁻ ω, ENNReal.ofReal |(Z + W) ω|^2 ∂P < ∞ := by
    have obs := add_mem_L2.2
    simp only [eLpNorm, OfNat.ofNat_ne_zero, ↓reduceIte, ENNReal.ofNat_ne_top, eLpNorm',
               Pi.add_apply, ENNReal.toReal_ofNat, ENNReal.rpow_ofNat, one_div] at obs
    have obs' := (ENNReal.rpow_inv_lt_iff two_pos).mp obs
    simp only [ENNReal.rpow_ofNat] at obs'
    convert obs' using 1
    simp [Real.enorm_eq_ofReal_abs]
  have ZW_indep' : P.map (fun ω ↦ (Z ω, W ω)) = (P.map Z).prod (P.map W) :=
    (indepFun_iff_map_prod_eq_prod_map_map Z_mble.aemeasurable W_mble.aemeasurable).mp ZW_indep
  have abs_sum_mble : Measurable (fun (xy : ℝ × ℝ) ↦ |xy.1 + xy.2|) :=
    Measurable.norm measurable_add
  have abs_sq_mble : Measurable (fun (x :  ℝ) ↦ ENNReal.ofReal |x| ^ 2) := by
    apply (measurable_pow.comp
            (show Measurable (fun (y : ℝ≥0∞) ↦ (⟨y, 2⟩ : ℝ≥0∞ × ℕ)) by measurability)).comp
    simp only [ENNReal.some_eq_coe, measurable_coe_nnreal_ennreal_iff]
    exact measurable_id.norm.real_toNNReal
  have abs_sum_sq_mble : Measurable (fun (xy : ℝ × ℝ) ↦ ENNReal.ofReal |xy.1 + xy.2| ^ 2) :=
    abs_sq_mble.comp measurable_add
  have normsq_add_eq :
      ∫⁻ ω, ENNReal.ofReal |(Z + W) ω|^2 ∂P
       = ∫⁻ zw, ENNReal.ofReal |(zw.1 + zw.2)|^2 ∂((P.map Z).prod (P.map W)) := by
    rw [← ZW_indep', lintegral_map]
    · simp
    · exact abs_sum_sq_mble
    · exact Measurable.prod Z_mble W_mble
  rw [lintegral_prod_symm _ abs_sum_sq_mble.aemeasurable] at normsq_add_eq
  have ae_finite : ∀ᵐ y ∂(P.map W),
          ∫⁻ (x : ℝ), ENNReal.ofReal |(x, y).1 + (x, y).2| ^ 2 ∂(P.map Z) < ∞ := by
    rw [normsq_add_eq] at normsq_add_finite
    refine ae_lt_top' ?_ normsq_add_finite.ne
    exact AEMeasurable.lintegral_prod_right (measurable_swap_iff.mp abs_sum_sq_mble).aemeasurable
  have law_W_proba : IsProbabilityMeasure (P.map W) :=
    Measure.isProbabilityMeasure_map W_mble.aemeasurable
  have law_Z_proba : IsProbabilityMeasure (P.map Z) :=
    Measure.isProbabilityMeasure_map Z_mble.aemeasurable
  obtain ⟨y₀, hy₀⟩ :
      ∃ y, ∫⁻ (x : ℝ), ENNReal.ofReal |(x, y).1 + (x, y).2| ^ 2 ∂(P.map Z) < ∞ := by
    have nebot_ae : Filter.NeBot (ae (P.map W)) := by
      have : IsProbabilityMeasure (P.map W) := Measure.isProbabilityMeasure_map W_mble.aemeasurable
      exact ae_neBot.mpr (NeZero.ne' (Measure.map W P)).symm
    exact ae_finite.exists
  have est (x) : x ^ 2 ≤ 2 * (x + y₀) ^ 2 + 2 * y₀ ^ 2 := by
    convert add_le_add (show x ^ 2 ≤ x ^ 2 from le_rfl)
            (show 0 ≤ (x + 2 * y₀) ^ 2 from sq_nonneg _) using 1 <;> ring
  have rwr (z : ℝ) : ENNReal.ofReal |z| ^ 2 = ENNReal.ofReal (z ^ 2) := by
    rw [(sq_abs z).symm, sq |z|, ENNReal.ofReal_mul, ← sq]
    exact abs_nonneg z
  have est' (x : ℝ) :
      ENNReal.ofReal |x| ^ 2 ≤ 2 * ENNReal.ofReal |x + y₀| ^ 2 + 2 * ENNReal.ofReal |y₀| ^ 2 := by
    simp only [rwr, ← mul_add]
    rw [← ENNReal.ofReal_add]
    · rw [show 2 * ENNReal.ofReal ((x + y₀) ^ 2 + y₀ ^ 2)
              = ENNReal.ofReal (2 * ((x + y₀) ^ 2 + y₀ ^ 2)) by
              simp [ENNReal.ofReal_mul zero_le_two]]
      apply ENNReal.ofReal_le_ofReal
      simpa only [mul_add] using est x
    · exact sq_nonneg (x + y₀)
    · exact sq_nonneg y₀
  suffices ∫⁻ (x : ℝ), ENNReal.ofReal |x| ^ 2 ∂(P.map Z) < ∞ by
    simp only [MemLp, eLpNorm, OfNat.ofNat_ne_zero, ↓reduceIte, ENNReal.ofNat_ne_top, eLpNorm',
               ENNReal.toReal_ofNat, ENNReal.rpow_ofNat, one_div]
    refine ⟨Z_mble.aestronglyMeasurable, (ENNReal.rpow_inv_lt_iff two_pos).mpr ?_⟩
    simp only [ENNReal.rpow_ofNat]
    convert this
    rw [lintegral_map abs_sq_mble Z_mble]
    simp [Real.enorm_eq_ofReal_abs]
  calc  ∫⁻ (x : ℝ), ENNReal.ofReal |x| ^ 2 ∂Measure.map Z P
      ≤ ∫⁻ (x : ℝ), (2 * ENNReal.ofReal |x + y₀| ^ 2 + 2 * ENNReal.ofReal |y₀| ^ 2)
                    ∂Measure.map Z P :=
          lintegral_mono est'
    _ = 2 * ∫⁻ (x : ℝ), ENNReal.ofReal |x + y₀| ^ 2 ∂Measure.map Z P + 2 * ∫⁻ (x : ℝ), ENNReal.ofReal |y₀| ^ 2 ∂Measure.map Z P := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul, lintegral_const_mul]
          · exact abs_sq_mble.comp measurable_const
          · exact abs_sq_mble.comp (Measurable.add_const measurable_id ..)
    _ < ⊤ := by
          simp only [lintegral_const, measure_univ, mul_one, ENNReal.add_lt_top]
          exact ⟨by finiteness, by finiteness⟩

lemma ProbabilityTheory.IndepFun.memLp_two_add_iff' {Z W : Ω → ℝ}
    (Z_mble : Measurable Z) (W_mble : Measurable W) (ZW_indep : IndepFun Z W P) :
    MemLp (Z + W) 2 P ↔ MemLp Z 2 P ∧ MemLp W 2 P := by
  constructor
  · intro hZW
    constructor
    · exact ZW_indep.memLp_of_memLp_add Z_mble W_mble hZW
    · apply ZW_indep.symm.memLp_of_memLp_add W_mble Z_mble
      simpa only [add_comm] using hZW
  · intro ⟨hZ, hW⟩
    exact MemLp.add hZ hW

lemma ProbabilityTheory.IndepFun.memLp_two_add_iff {Z W : Ω → ℝ}
    (Z_mble : AEStronglyMeasurable Z P) (W_mble : AEStronglyMeasurable W P)
    (ZW_indep : IndepFun Z W P) :
    MemLp (Z + W) 2 P ↔ MemLp Z 2 P ∧ MemLp W 2 P := by
  obtain ⟨Z', Z'_mble, _, hZ'⟩ :=
    Z_mble.aemeasurable.exists_ae_eq_range_subset (by simp) Set.univ_nonempty
  obtain ⟨W', W'_mble, _, hW'⟩ :=
    W_mble.aemeasurable.exists_ae_eq_range_subset (by simp) Set.univ_nonempty
  have add_ae_eq : Z + W =ᵐ[P] Z' + W' := EventuallyEq.add hZ' hW'
  rw [memLp_congr_ae hZ', memLp_congr_ae hW', memLp_congr_ae add_ae_eq]
  apply memLp_two_add_iff' Z'_mble W'_mble (ZW_indep.congr hZ' hW')

lemma ProbabilityTheory.IndepFun.evariance_add {Z W : Ω → ℝ}
    (Z_mble : AEStronglyMeasurable Z P) (W_mble : AEStronglyMeasurable W P) (h : IndepFun Z W P) :
    eVar[Z + W; P] = eVar[Z; P] + eVar[W; P] := by
  have key : MemLp (Z + W) 2 P ↔ MemLp Z 2 P ∧ MemLp W 2 P := memLp_two_add_iff Z_mble W_mble h
  by_cases sum_mem_L2 : MemLp (Z + W) 2 P
  · have Z_mem_L2 : MemLp Z 2 P := by tauto
    have W_mem_L2 : MemLp W 2 P := by tauto
    suffices Var[Z + W; P] = Var[Z; P] + Var[W; P] by
      simp [variance] at this
      rw [← ENNReal.toReal_add Z_mem_L2.evariance_ne_top W_mem_L2.evariance_ne_top] at this
      refine ENNReal.toReal_eq_toReal_iff' ?_ ?_ |>.1 this
      · exact sum_mem_L2.evariance_ne_top
      · simp [Z_mem_L2.evariance_ne_top, W_mem_L2.evariance_ne_top]
    exact variance_add Z_mem_L2 W_mem_L2 h
  · have one_not_mem_L2 : ¬ MemLp Z 2 P ∨ ¬ MemLp W 2 P := by tauto
    cases' one_not_mem_L2 with Z_not_mem_L2 W_not_mem_L2
    · rw [← evariance_eq_top_iff (by measurability)] at Z_not_mem_L2 sum_mem_L2
      simp [Z_not_mem_L2, sum_mem_L2]
    · rw [← evariance_eq_top_iff (by measurability)] at W_not_mem_L2 sum_mem_L2
      simp [W_not_mem_L2, sum_mem_L2]

omit [IsProbabilityMeasure P] in
lemma indepFun_sum_term' {ι : Type*} {I : Finset ι} {Z : ι → Ω → ℝ}
     (Z_mble : ∀ i, Measurable (Z i)) (Z_indep : iIndepFun Z P) {j : ι} (hj : j ∉ I) :
     IndepFun (∑ i ∈ I, Z i) (Z j) P := by
  convert @IndepFun.comp Ω (Π (i : I), ℝ) ℝ ℝ ℝ _ P (fun ω i ↦ Z i ω) (Z j)
          MeasurableSpace.pi Real.measurableSpace Real.measurableSpace Real.measurableSpace
          (fun t ↦ ∑ i, t i) id ?_ (by measurability) measurable_id
  · funext ω
    simp only [Finset.sum_apply, Finset.univ_eq_attach, Function.comp_apply]
    rw [Finset.sum_of_injOn (s := I.attach) (f := fun i ↦ Z i ω) (g := fun i ↦ Z i ω)
            (fun i ↦ i) Set.injOn_subtype_val (by aesop) (by aesop) (by aesop)]
  · let J : Finset ι := {j}
    have key : IndepFun (fun ω (i : I) ↦ Z i ω) (fun ω (i : J) ↦ Z i ω) P := by
      apply Kernel.iIndepFun.indepFun_finset I J _ Z_indep Z_mble
      exact Finset.disjoint_singleton_right.mpr hj
    apply IndepFun.comp (ψ := fun f ↦ f ⟨j, Finset.mem_singleton.mpr rfl⟩) key measurable_id
    measurability

omit [IsProbabilityMeasure P] in
lemma indepFun_sum_term {ι : Type*} {I : Finset ι} {Z : ι → Ω → ℝ}
     (Z_mble : ∀ i, AEStronglyMeasurable (Z i) P) (Z_indep : iIndepFun Z P) {j : ι} (hj : j ∉ I) :
     IndepFun (∑ i ∈ I, Z i) (Z j) P := by
  have aux (i : ι) : ∃ W, Measurable W ∧ Z i =ᵐ[P] W := by
    obtain ⟨W, W_mble, hW⟩ :=
      (Z_mble i).exists_stronglyMeasurable_range_subset MeasurableSet.univ Set.univ_nonempty
            (by simp)
    exact ⟨W, W_mble.measurable, by simpa using hW⟩
  let W : ι → Ω → ℝ := fun i ↦ Classical.choose (aux  i)
  let W_mble := fun i ↦ (Classical.choose_spec (aux i)).1
  let W_eq := fun i ↦ (Classical.choose_spec (aux i)).2
  have key := indepFun_sum_term' W_mble (iIndepFun.congr W_eq Z_indep) hj
  apply IndepFun.congr key
  · exact (eventuallyEq_sum fun i a ↦ W_eq i).symm
  · exact (W_eq j).symm

lemma ProbabilityTheory.evariance_sum {ι : Type*} [DecidableEq ι]
    {I : Finset ι} {Z : ι → Ω → ℝ} (Z_mble : ∀ i, AEStronglyMeasurable (Z i) P)
    (Z_indep : iIndepFun Z P) :
    eVar[∑ i ∈ I, Z i; P] = ∑ i ∈ I, eVar[Z i; P] := by
  induction' I using Finset.induction_on with a I ha ih
  · simp
  · simp_rw [Finset.sum_insert ha]
    rw [IndepFun.evariance_add, ih]
    · exact Z_mble a
    · exact Finset.aestronglyMeasurable_sum I fun i a ↦ Z_mble i
    · exact (indepFun_sum_term Z_mble Z_indep ha).symm

variable {X : ℕ → Ω → ℝ} (X_mble : ∀ n, Measurable (X n)) (X_indep : iIndepFun X P)
variable {b : ℝ} (X_ae_le_b : ∀ n, |X n| ≤ᵐ[P] (fun _ ↦ b))
variable (X_zeromean : ∀ n, ∫ ω, X n ω ∂P = 0)

lemma eLpNorm_two_sq_sum_terms_eq_sum_evariance (n : ℕ) (X_intble : ∀ n, Integrable (X n) P)
    (X_zeromean : ∀ n, ∫ ω, X n ω ∂P = 0) (X_indep : iIndepFun X P) :
    (eLpNorm (∑ i ∈ Finset.range n, X i) 2 P)^2
      = ∑ i ∈ Finset.range n, eVar[X i; P] := by
  rw [← evariance_eq_eLpNorm_two_sq_of_mean_zero]
  · rw [ProbabilityTheory.evariance_sum ?_ X_indep]
    exact fun i ↦ (X_intble i).aestronglyMeasurable
  · simp_rw [Finset.sum_apply]
    rw [integral_finset_sum _ (fun i _ ↦ X_intble i)]
    simp [X_zeromean]
