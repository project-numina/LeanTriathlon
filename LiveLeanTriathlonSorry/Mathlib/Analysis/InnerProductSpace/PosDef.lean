/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import LiveLeanTriathlonSorry.Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

namespace LinearMap

open scoped ComplexOrder

def IsPosDef {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (T : E →ₗ[𝕜] E) : Prop :=
  T.IsPositive ∧ T.det ≠ 0

namespace IsPosDef

lemma isPositive {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : E →ₗ[ℝ] E} (h : IsPosDef T) : T.IsPositive := h.1

lemma isSymmetric {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : E →ₗ[ℝ] E} (h : IsPosDef T) : T.IsSymmetric := h.1.1

lemma det_pos {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : IsPosDef T) : 0 < T.det :=
  hT.1.det_nonneg.lt_of_ne' hT.2

lemma add_Positive {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {T S : E →ₗ[𝕜] E} (hT : IsPosDef T) (hS : S.IsPositive) :
    LinearMap.IsPosDef (T + S) := by
  refine ⟨hT.1.add hS, ?_⟩
  obtain ⟨ι, b, hb⟩ := exists_orthonormalBasis 𝕜 E
  classical
  rw [← (T + S).det_toMatrix b.toBasis, map_add]
  refine (Matrix.PosDef.det_pos <| .add_posSemidef ((T.posSemidef_toMatrix_iff
    b|>.2 hT.1).posDef_iff_isUnit.2 ?_) <| S.posSemidef_toMatrix_iff b|>.2 hS).ne'
  rw [Matrix.isUnit_iff_isUnit_det, LinearMap.det_toMatrix]
  exact hT.2.isUnit

lemma eigenvalues_pos {E : Type*} {n} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hn : Module.finrank ℝ E = n) [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E}
    (hT : T.IsPosDef) (i) : 0 < hT.1.1.eigenvalues hn i :=
  (hT.1.nonneg_eigenvalues hn i).lt_of_ne' (fun h ↦
    hT.2 <| hT.1.1.det_eq_prod_eigenvalues hn ▸ Finset.prod_eq_zero (Finset.mem_univ i) h)

lemma isSymmetric_inv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} (hT : T.IsPosDef) :
    (T.equivOfDetNeZero hT.2).symm.IsSymmetric := fun x y ↦ by
  nth_rw 1 [← (T.equivOfDetNeZero hT.2).apply_symm_apply y, LinearEquiv.ofIsUnitDet_apply,
    ← hT.1.1]
  congr 1
  exact (T.equivOfDetNeZero hT.2).apply_symm_apply x

lemma isPositive_inv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} (hT : T.IsPosDef) :
    (T.equivOfDetNeZero hT.2).symm.toLinearMap.IsPositive := by
  refine ⟨hT.isSymmetric_inv, fun x ↦ ?_⟩
  convert @real_inner_comm E .. ▸ hT.1.2 ((T.equivOfDetNeZero hT.2).symm x)
  exact (T.equivOfDetNeZero hT.2).apply_symm_apply x |>.symm

lemma inv_eigenval {E : Type*} {n} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hn : Module.finrank ℝ E = n) [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} (hT : T.IsPosDef) (i) :
    (T.equivOfDetNeZero hT.2).symm.toLinearMap (hT.1.1.eigenvectorBasis hn i) =
      (hT.1.1.eigenvalues hn i)⁻¹ • (hT.1.1.eigenvectorBasis hn i) := by
  convert (congr((HSMul.hSMul (hT.1.1.eigenvalues hn i)⁻¹) $(congr(
    (T.equivOfDetNeZero hT.2).symm.toLinearMap $(hT.1.1.apply_eigenvectorBasis hn i))))).symm using 1
  · rw [map_smul, ← SemigroupAction.mul_smul]
    change _ = ((hT.1.1.eigenvalues hn i)⁻¹ * hT.1.1.eigenvalues hn i) • _
    rw [inv_mul_cancel₀ (hT.eigenvalues_pos hn i).ne', one_smul]
  · exact congr_arg _ ((T.equivOfDetNeZero hT.2).symm_apply_apply _).symm

open Polynomial

lemma inv_charpoly {E : Type*} {n} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hn : Module.finrank ℝ E = n) [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} (hT : T.IsPosDef) :
    (T.equivOfDetNeZero hT.2).symm.toLinearMap.charpoly =
      ∏ i, (X (R := ℝ) - C (hT.1.1.eigenvalues hn i)⁻¹) := by
  rw [← (T.equivOfDetNeZero hT.2).symm.toLinearMap.charpoly_toMatrix
    (hT.1.1.eigenvectorBasis hn).toBasis]
  convert Matrix.charpoly_diagonal (fun i ↦ (hT.1.1.eigenvalues hn i)⁻¹)
  ext i j
  simp +contextual [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, hT.inv_eigenval, Matrix.diagonal_apply]

lemma eigenvalues_inv {E : Type*} {n} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hn : Module.finrank ℝ E = n) [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} (hT : T.IsPosDef) :
    hT.isSymmetric_inv.eigenvalues hn = fun i ↦ (hT.1.1.eigenvalues hn (Fin.rev i))⁻¹ := by
  let lam := hT.1.1.eigenvalues hn
  let lam_inv := hT.isSymmetric_inv.eigenvalues hn
  have h_perm1 : List.Perm (List.ofFn lam_inv) (List.ofFn (fun j => (lam j)⁻¹)) := by
    rw [← Multiset.coe_eq_coe, ← Fin.univ_val_map, ← Fin.univ_val_map]
    simp +zetaDelta [← Multiset.bind_singleton, ← Polynomial.roots_X_sub_C,
      ← Polynomial.roots_prod (fun i ↦ X - C (lam_inv i)) _ (by
      simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]),
      ← Polynomial.roots_prod (fun i ↦ X - C ((lam i)⁻¹)) _ (by simp
      [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]),
      ← hT.inv_charpoly hn, hT.isSymmetric_inv.charpoly_eq hn]
  refine List.ofFn_injective <| (h_perm1.trans <| by simpa [Function.comp_def] using
    (Equiv.Perm.ofFn_comp_perm Fin.revPerm fun j => (lam j)⁻¹).symm).eq_of_pairwise
    (fun _ _ _ _ ↦ ge_antisymm) ?_ ?_
  <;> refine List.sortedGE_iff_pairwise.1 (List.sortedGE_ofFn_iff.2 ?_)
  · exact hT.isSymmetric_inv.eigenvalues_antitone hn
  · exact fun _ _ h ↦ inv_anti₀ (hT.eigenvalues_pos hn _) <| hT.1.1.eigenvalues_antitone hn <|
      Fin.rev_le_rev.2 h

lemma opNorm_inv_eq {E : Type*} {n} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hn : Module.finrank ℝ E = n) [FiniteDimensional ℝ E] (hE : n ≠ 0) {T : E →ₗ[ℝ] E}
    (hT : T.IsPosDef) : let index_last : Fin n := ⟨n - 1, Nat.pred_lt hE⟩
    ‖(T.equivOfDetNeZero hT.2).symm.toContinuousLinearMap‖ =
    (hT.isSymmetric.eigenvalues hn index_last)⁻¹ :=
  have : NeZero n := ⟨hE⟩
  Eq.trans (b := hT.isSymmetric_inv.eigenvalues hn ⟨0, Nat.zero_lt_of_ne_zero hE⟩)
    (hT.isPositive_inv.opNorm_eq_top_eigenvalue hn) <| congr_fun (hT.eigenvalues_inv hn) _
