/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import LiveLeanTriathlonSorry.Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Matrix.PosDef

@[expose] public section

namespace LinearMap.IsPositive

open scoped ComplexOrder

lemma det_nonneg' {ι 𝕜 E : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {T : E →ₗ[𝕜] E} (hT : T.IsPositive) (b : OrthonormalBasis ι 𝕜 E) :
    0 ≤ T.det := LinearMap.det_toMatrix b.toBasis T ▸
  Matrix.PosSemidef.det_nonneg <| LinearMap.posSemidef_toMatrix_iff b|>.2 hT

lemma det_nonneg {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsPositive) : 0 ≤ T.det := by
  obtain ⟨ι, b, hb⟩ := exists_orthonormalBasis 𝕜 E
  classical exact hT.det_nonneg' b

lemma sum {ι 𝕜 E : Type*} [RCLike 𝕜] [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {f : ι → E →ₗ[𝕜] E} (hf : ∀ i, (f i).IsPositive) : (∑ i, (f i)).IsPositive := by
  classical induction Finset.univ (α := ι) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => exact Finset.sum_insert (M := E →ₗ[𝕜] E) ha ▸ IsPositive.add (hf a) ih

lemma opNorm_eq_top_eigenvalue {E 𝕜 : Type*} {n} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (hn : Module.finrank 𝕜 E = n) [FiniteDimensional 𝕜 E]
    [NeZero n] {T : E →ₗ[𝕜] E} (hT : T.IsPositive) :
    ‖T.toContinuousLinearMap‖ = hT.isSymmetric.eigenvalues hn 0 := by
  let B := hT.1.eigenvectorBasis hn
  let eigs := hT.1.eigenvalues hn
  refine le_antisymm (ContinuousLinearMap.opNorm_le_of_unit_norm (hT.nonneg_eigenvalues hn _)
    fun x hx ↦ ?_) <| le_trans (b := ‖eigs 0‖) (le_abs_self _) <| by
      simpa using ContinuousLinearMap.hasEigenvalue_le_opNorm T.toContinuousLinearMap
        (hT.1.hasEigenvalue_eigenvalues hn 0)
  rw [← B.repr.norm_map _, ← Real.sqrt_sq (norm_nonneg _)]
  grw [Real.sqrt_le_sqrt (_ : _ ≤ (eigs 0) ^ 2), Real.sqrt_sq (hT.nonneg_eigenvalues hn _)]
  rw [EuclideanSpace.norm_sq_eq]
  simp only [coe_toContinuousLinearMap', B, hT.1.eigenvectorBasis_apply_self_apply, norm_mul,
    RCLike.norm_ofReal, abs_of_nonneg (hT.nonneg_eigenvalues hn _)]
  refine le_of_le_of_eq (Finset.sum_le_sum fun i _ ↦ sq_le_sq₀ ?_ ?_ |>.2 ?_ :
    _ ≤ ∑ i, (eigs 0 * ‖(B.repr x).ofLp i‖) ^ 2) ?_
  all_goals try exact mul_nonneg (hT.nonneg_eigenvalues hn _) (norm_nonneg _)
  · grw [hT.1.eigenvalues_antitone hn (Fin.zero_le i)]
  · simp [mul_pow, ← Finset.mul_sum, ← EuclideanSpace.norm_sq_eq, B.repr.norm_map, hx]

lemma mono {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B : E →ₗ[ℝ] E} (h : A ≤ B) : A.IsPositive → B.IsPositive :=
  fun hA ↦ by simpa using hA.add ((LinearMap.le_def A B).mp h)

lemma _root_.inner_le_of_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B : E →ₗ[ℝ] E} (h : A ≤ B) (x : E) :
    inner ℝ (A x) x ≤ inner ℝ (B x) x := by
  rw [← sub_nonneg, ← inner_sub_left, ← LinearMap.sub_apply]
  exact h.inner_nonneg_left x

lemma _root_.inner_apply_eigenBasis_left {E : Type*} {n} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hn : Module.finrank ℝ E = n) [FiniteDimensional ℝ E] {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric) (i) :
    inner ℝ (A (hA.eigenvectorBasis hn i)) (hA.eigenvectorBasis hn i) = hA.eigenvalues hn i := by
  simp [hA.apply_eigenvectorBasis hn, inner_smul_left]

lemma opNorm_le_of_le {E : Type*} {n} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hn : Module.finrank ℝ E = n) [FiniteDimensional ℝ E] {A B : E →ₗ[ℝ] E} (hA : A.IsPositive)
    (h : A ≤ B) :
    ‖A.toContinuousLinearMap‖ ≤ ‖B.toContinuousLinearMap‖ := by
  if hn' : n = 0 then
  have : Subsingleton E := Module.finrank_zero_iff.1 (hn ▸ hn')
  simp [Subsingleton.elim A 0, Subsingleton.elim B 0] else
  have : NeZero n := ⟨hn'⟩
  let v := hA.1.eigenvectorBasis hn 0
  rw [hA.opNorm_eq_top_eigenvalue hn, ← inner_apply_eigenBasis_left hn hA.1 0]
  grw (transparency := default) [inner_le_of_le h, real_inner_le_norm,
    B.toContinuousLinearMap.le_opNorm v]
  simp [v, (hA.1.eigenvectorBasis hn).orthonormal.1 0]

lemma bot_eigenvalue_le_of_le {E : Type*} {n} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (hn : Module.finrank ℝ E = n) [FiniteDimensional ℝ E]
    (hn' : n ≠ 0) {A B : E →ₗ[ℝ] E} (hA : A.IsPositive) (h : A ≤ B) :
    hA.1.eigenvalues hn ⟨n - 1, n.pred_lt hn'⟩ ≤
      (mono h hA).1.eigenvalues hn ⟨n - 1, n.pred_lt hn'⟩ := by
  let n' : Fin n := ⟨n - 1, Nat.pred_lt hn'⟩
  let bB := (mono h hA).1.eigenvectorBasis hn
  let bA := hA.1.eigenvectorBasis hn
  have h_inner_A_eB : inner ℝ (A (bB n')) (bB n') =
      ∑ j : Fin n, (hA.1.eigenvalues hn j) * (inner ℝ (bA j) (bB n')) ^ 2 := by
    conv_lhs => rw [← bA.sum_repr' (bB n'), map_sum]
    simp_rw [LinearMap.map_smul, bA, hA.1.apply_eigenvectorBasis hn, smul_smul]
    rw [sum_inner, ← bA.sum_repr' (bB n')]
    simp_rw [inner_smul_left, RCLike.conj_to_real, inner_sum, inner_smul_right,
      (hA.1.eigenvectorBasis hn).inner_eq_ite, mul_boole, Fintype.sum_ite_eq]
    congr! 1 with j _
    simpa +zetaDelta using by ring
  rw [← mul_one (hA.1.eigenvalues _ _), ← @one_pow ℝ _ 2, ← bB.orthonormal.1 n',
    ← bA.sum_sq_inner_right (bB n'), Finset.mul_sum]
  refine le_trans' (b := ∑ j, hA.1.eigenvalues hn j * (inner ℝ (bA j) (bB n')) ^ 2) ?_ <|
    Finset.sum_le_sum fun j _ ↦ by gcongr; exact hA.1.eigenvalues_antitone hn (by grind)
  grw [← h_inner_A_eB, inner_le_of_le h (bB n'), inner_apply_eigenBasis_left hn _ n']
