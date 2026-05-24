/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Data.Real.Hom

@[expose] public section

namespace Matrix

lemma gram_not_PosDef_det {E I : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : I → E)
    (h : ¬ (gram ℝ v).PosDef) :
    (gram ℝ v).det = 0 := by_contra fun h1 ↦ h <| (posSemidef_gram ℝ _).posDef_iff_isUnit.2 <|
  (gram ℝ v).isUnit_iff_isUnit_det.2 <| Ne.isUnit h1

lemma submatrix_gram' {E n 𝕜 m : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (v : n → E) (f : m → n) :
    (Matrix.gram 𝕜 v).submatrix f f = Matrix.gram 𝕜 (v ∘ f) := by rfl

lemma det_gram_eq_prod_infDist {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype I] [LinearOrder I] (v : I → E) : (Matrix.gram ℝ v).det =
    ∏ i, (Metric.infDist (v i) (Submodule.span ℝ (v '' Set.Ioi i)))^2 := by
  generalize hn : Fintype.card I = n
  induction n generalizing I v with
  | zero => simp [Fintype.card_eq_zero_iff.1 hn]
  | succ n IH =>
    have hI : Nonempty I := Fintype.card_pos_iff.1 <| by grind
    let i₀ := @Finset.min' I _ Finset.univ Finset.univ_nonempty
    let J := Set.Ioi i₀
    have hJ1 : J = Finset.univ.erase i₀ := Set.ext fun i ↦ by
      simpa +zetaDelta using ⟨ne_of_gt, fun h ↦ lt_of_le_of_ne
        (Finset.min'_le _ i (Finset.mem_univ _)) (Ne.symm h)⟩
    have hnJ : Fintype.card J = n := by
      simp [hJ1]
      rw [Fintype.card_subtype (Membership.mem (Set.univ \ {i₀}))]
      simp only [Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and]
      have : ({x : I | ¬x = i₀} : Finset I) = Finset.univ \ {i₀} := by
        ext
        simp
      rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ {i₀})]
      simp [hn]
    specialize IH (Set.restrict J v) hnJ
    let v₀ := v i₀
    let S := Submodule.span ℝ (v '' J)
    let u := v₀ - S.starProjection v₀
    have hu : ‖u‖ = Metric.infDist v₀ S := by
      simp [u, Submodule.starProjection_minimal, Metric.infDist_eq_iInf, dist_eq_norm]
    suffices (Matrix.gram ℝ v).det = (inner ℝ u u) * (Matrix.gram ℝ (J.restrict v)).det by
      set f := fun i ↦ Metric.infDist (v i) ↑(Submodule.span ℝ (v '' (Set.Ioi i))) ^ 2
      rw [this]
      sorry

    clear * - u hJ1
    by_cases hw1 : LinearIndependent ℝ (J.restrict v)
    · let e : {i : I | i = i₀} ⊕ {i : I | ¬(i = i₀)} ≃ I := Equiv.sumCompl (· = i₀)
      have hJ2 : {i : I | ¬(i = i₀)} = J := by ext; simp [hJ1]
      let e_J : {i : I | ¬(i = i₀)} ≃ J := Equiv.setCongr hJ2
      have hv01 : inner ℝ v₀ v₀ - inner ℝ v₀ (S.starProjection v₀) =
          inner ℝ u u := by
        conv_lhs => enter [1]; rw [← sub_add_cancel v₀ (S.starProjection v₀), inner_add_left]
        rw [inner_add_right, inner_add_right, Submodule.starProjection_inner_eq_zero _
          (S.starProjection v₀) (by simp), Submodule.sub_starProjection_mem_orthogonal v₀
          (S.starProjection v₀) (by simp)]
        ring_nf
        nth_rw 2 [← add_zero (inner ℝ u u)]
        rw [add_sub_assoc, add_right_inj, sub_eq_zero,
          Submodule.inner_starProjection_left_eq_right,
          ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def,
          S.isIdempotentElem_starProjection]
      let sing := {i : I | i = i₀}
      let compl := {i : I | ¬i = i₀}
      let A : Matrix sing sing ℝ := Matrix.of fun _ _ => inner ℝ v₀ v₀
      let B : Matrix sing compl ℝ := Matrix.of fun _ j => inner ℝ v₀ (v j.val)
      let C : Matrix compl sing ℝ := Matrix.of fun i _ => inner ℝ (v i.val) v₀
      let D' : Matrix compl compl ℝ := Matrix.of fun i j => inner ℝ (v i.val) (v j.val)
      have h_block_eq : Matrix.fromBlocks A B C D' = (gram ℝ v).submatrix e e := by
        have hi1 (i : sing) : e (Sum.inl i) = i.val := Equiv.sumCompl_apply_inl (p := (· = i₀)) i
        have hi2 (i : compl) : e (Sum.inr i) = i.val := Equiv.sumCompl_apply_inr (p := (· = i₀)) i
        have hj1 (j : sing) : e (Sum.inl j) = j.val := Equiv.sumCompl_apply_inl (p := (· = i₀)) j
        have hj2 (j : compl) : e (Sum.inr j) = j.val := Equiv.sumCompl_apply_inr (p := (· = i₀)) j
        ext (i | i) (j | j)
        all_goals simp_all +zetaDelta only [fromBlocks_apply₁₁, fromBlocks_apply₁₂,
          Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, of_apply, submatrix_apply, gram]
        · rw [i.2, j.2]
        · rw [i.2]
        · rw [j.2]
      have hD'_isUnit : IsUnit D' := by
        rw [show D' = (gram ℝ (J.restrict v)).submatrix (fun i => e_J i) (fun j => e_J j) from
          (Equiv.apply_eq_iff_eq_symm_apply of).2 rfl, Matrix.isUnit_iff_isUnit_det,
          Matrix.det_submatrix_equiv_self, ← Matrix.isUnit_iff_isUnit_det]
        exact (gram ℝ _).isUnit_iff_isUnit_det.2 <| Ne.isUnit <| ne_of_gt
          (posDef_gram_of_linearIndependent hw1).det_pos
      let : Invertible D' := hD'_isUnit.invertible
      simp only [← det_submatrix_equiv_self e, ← h_block_eq, det_fromBlocks₂₂,
        @det_eq_elem_of_subsingleton _ _ _ _ _ (by simp [sing]) (A - B * ⅟D' * C) ⟨i₀, rfl⟩]
      let c : compl → ℝ := fun i => ∑ j, ⅟D' i j * (inner ℝ (v j.1) v₀)
      have hk (k) (hk : k ≠ i₀) : inner ℝ (v₀ - ∑ i, c i • v i.1) (v k) = 0 := by
        simp only [inner_sub_left, sum_inner, inner_smul_left, starRingEnd_apply, star_trivial,
          c, Finset.sum_mul]
        simp_rw +singlePass [Finset.sum_comm, mul_comm (⅟D' _ _), mul_assoc, ← Finset.mul_sum]
        conv_lhs => enter [2, 2, i, 2]; tactic =>
          convert (mul_apply (M := D') (N := ⅟D') (i := ⟨k, hk⟩) (k := i)).symm using 1
          simp [D', mul_comm, real_inner_comm]
        simp [one_apply, real_inner_comm]
      have h_proj_eq : S.starProjection v₀ = ∑ i, c i • v i.val := by
        refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ (fun x hx ↦ ?_)
        · exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ <|
            Submodule.subset_span ⟨i, by simpa [-Subtype.coe_prop, *] using i.2, rfl⟩
        · induction hx using Submodule.span_induction with
          | mem y hy =>
            simp only [Set.mem_image, J, Set.mem_Ioi] at hy
            exact hy.choose_spec.2 ▸ hk hy.choose (ne_of_gt hy.choose_spec.1)
          | zero => simp
          | add x y _ _ hx hy => simp [inner_add_right, hx, hy]
          | smul r x _ hx => simp [inner_smul_right, hx]
      convert_to D'.det * inner ℝ u u = _
      · simp only [sub_apply, mul_apply, A, B, C, of_apply, ← hv01]
        congr 1
        simp only [inner_self_eq_norm_sq_to_K, Real.ringHom_apply, real_inner_comm, c,
          invOf_eq_nonsing_inv, mul_comm, h_proj_eq, inner_sum, inner_smul_right, sub_right_inj]
        congr! 4 with i _ j
        exact (IsSymm.inv <| by ext; simp [D', real_inner_comm]).apply _ _
      · rw [show D' = (gram ℝ (J.restrict v)).submatrix (fun i => e_J i) (fun j => e_J j)
        from (Equiv.apply_eq_iff_eq_symm_apply of).2 rfl, det_submatrix_equiv_self, mul_comm]
    · have hv1 : ¬(gram ℝ v).PosDef := fun h ↦ (fun h ↦ hw1 <|
        LinearIndepOn.linearIndependent_restrict (linearIndepOn_iff.2 fun _ _ a ↦ h a))
        (posDef_gram_iff_linearIndependent.1 h)
      rw [gram_not_PosDef_det v hv1, gram_not_PosDef_det _
        (by rwa [posDef_gram_iff_linearIndependent]), mul_zero]

theorem gram_eq_conj_mul {E : Type*} {n m} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : Fin m → E) {o : Module.Basis (Fin n) ℝ E}
    (ho : Orthonormal ℝ o) : gram ℝ b = (o.toMatrix b)ᵀ * (o.toMatrix b) := Matrix.ext fun i j ↦ by
  simp only [gram_apply, mul_apply, transpose_apply, ← Module.Basis.sum_toMatrix_smul_self o b,
    inner_sum, inner_smul_right, sum_inner]
  simp [inner_smul_left, orthonormal_iff_ite.1 ho, mul_comm]
