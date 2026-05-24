/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import LiveLeanTriathlonSorry.Mathlib.Analysis.InnerProductSpace.Symmetric

@[expose] public section

namespace LinearMap

variable {𝕜 E F : Type*} {n : ℕ} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (hn : Module.finrank 𝕜 E = n) [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (l : E →ₗ[𝕜] F)

noncomputable def singularValuesFin' : Fin n → ℝ :=
  Real.sqrt ∘ ((LinearMap.isPositive_adjoint_comp_self l).1.eigenvalues hn)

lemma singularValuesFin'_def (i : Fin n) : l.singularValuesFin' hn i =
    Real.sqrt ((LinearMap.isPositive_adjoint_comp_self l).1.eigenvalues hn i) :=
  rfl

lemma singularValuesFin'_nonneg (i : Fin n) : 0 ≤ l.singularValuesFin' hn i :=
  Real.sqrt_nonneg _

lemma antitone_singularValuesFin' : Antitone (l.singularValuesFin' hn) := fun x y hxy ↦ by
  simp only [singularValuesFin'_def, Real.sqrt_le_iff, Real.sqrt_nonneg, true_and]
  rw [Real.sq_sqrt ((isPositive_adjoint_comp_self l).nonneg_eigenvalues hn x)]
  exact (isPositive_adjoint_comp_self l).left.eigenvalues_antitone hn hxy

lemma mem_range_singularValuesFin' (σ : ℝ) :
    σ ∈ Set.range (l.singularValuesFin' hn) ↔ σ ^ 2 ∈ Set.range
      (l.isPositive_adjoint_comp_self.1.eigenvalues hn) ∧ 0 ≤ σ :=
  ⟨fun ⟨i, hi⟩ ↦ ⟨⟨i, hi ▸ l.singularValuesFin'_def hn i ▸ Real.sq_sqrt
  ((LinearMap.isPositive_adjoint_comp_self l).nonneg_eigenvalues hn i) |>.symm⟩,
  hi ▸ l.singularValuesFin'_def hn i ▸ Real.sqrt_nonneg _⟩, fun ⟨⟨i, hi⟩, hσ⟩ ↦ ⟨i,
  l.singularValuesFin'_def hn i ▸ hi ▸ Real.sqrt_sq hσ⟩⟩

theorem IsSymmetric.mem_range_eigenvalues  {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (μ : 𝕜)
    (hμ : Module.End.HasEigenvalue T μ) : ∃ i, hT.eigenvalues hn i = μ := by
  obtain ⟨v, hv_mem, hv_ne⟩ := hμ.exists_hasEigenvector
  let B := hT.eigenvectorBasis hn
  have h_ne_zero : B.repr v ≠ 0 := fun h ↦ hv_ne <| B.repr.injective (map_zero B.repr ▸ h)
  obtain ⟨i, hi⟩ : ∃ i, B.repr v i ≠ 0 := by_contra fun h ↦ h_ne_zero <|
    PiLp.ext fun j ↦ (by simpa using h : ∀ j, (B.repr v).ofLp j = 0) j
  have h_diag := hT.eigenvectorBasis_apply_self_apply hn v i
  replace h_diag : μ = hT.eigenvalues hn i ∨ (B.repr v).ofLp i = 0 := by
    simpa [Module.End.mem_eigenspace_iff.1 hv_mem] using h_diag
  exact ⟨i, by simpa [hi, eq_comm] using h_diag⟩

lemma adjoin_comp_self_eigenvals {f : E →ₗ[𝕜] E} :
    ∀ σ ∈ Set.range (f.isPositive_adjoint_comp_self.1.eigenvalues hn),
    σ ≠ 0 → σ ∈ Set.range (f.isPositive_self_comp_adjoint.1.eigenvalues hn) := fun σ ⟨i, hi⟩ h2 ↦ by
  have hspec : (σ : 𝕜) ∈ spectrum 𝕜 (f.adjoint * f) \ {0} := ⟨Module.End.hasEigenvalue_iff_mem_spectrum.1
    (hi ▸ f.isPositive_adjoint_comp_self.1.hasEigenvalue_eigenvalues hn i), by simpa⟩
  rw [spectrum.nonzero_mul_comm] at hspec
  simpa using f.isPositive_self_comp_adjoint.1.mem_range_eigenvalues hn σ <|
    Module.End.hasEigenvalue_iff_mem_spectrum.2 hspec.1

lemma self_comp_adjoin_eigenvals {f : E →ₗ[𝕜] E} :
    ∀ σ ∈ Set.range (f.isPositive_self_comp_adjoint.1.eigenvalues hn),
    σ ≠ 0 → σ ∈ Set.range (f.isPositive_adjoint_comp_self.1.eigenvalues hn) := fun σ ⟨i, hi⟩ h2 ↦ by
  have h1 : (σ : 𝕜) ∈ spectrum 𝕜 (f * f.adjoint) \ {0} := ⟨Module.End.hasEigenvalue_iff_mem_spectrum.1
    (hi ▸ f.isPositive_self_comp_adjoint.1.hasEigenvalue_eigenvalues hn i), by simpa⟩
  rw [spectrum.nonzero_mul_comm] at h1
  simpa using  f.isPositive_adjoint_comp_self.1.mem_range_eigenvalues hn σ <|
    Module.End.hasEigenvalue_iff_mem_spectrum.2 h1.1

lemma adjoin_comp_eigenval_iff {f : E →ₗ[𝕜] E} {σ : ℝ} (hσ : σ ≠ 0) :
    σ ∈ Set.range (f.isPositive_adjoint_comp_self.1.eigenvalues hn) ↔
    σ ∈ Set.range (f.isPositive_self_comp_adjoint.1.eigenvalues hn) :=
  ⟨fun h ↦ adjoin_comp_self_eigenvals hn σ h hσ, fun h ↦ self_comp_adjoin_eigenvals hn σ h hσ⟩

lemma adjoin_singularValue_eq {f : E →ₗ[𝕜] E} : Set.range (f.singularValuesFin' hn) \ {0} =
    Set.range (f.adjoint.singularValuesFin' hn) \ {0} := Set.ext fun σ ↦ ⟨fun h ↦ by
  obtain ⟨h, hσ⟩ := by simpa only [Set.mem_diff, Set.mem_singleton_iff] using h
  obtain ⟨h1, h2⟩ := f.mem_range_singularValuesFin' hn σ |>.1 h
  refine ⟨f.adjoint.mem_range_singularValuesFin' hn σ |>.2 ⟨?_, h2⟩, by simpa⟩
  convert f.adjoin_comp_eigenval_iff hn (by grind) |>.1 h1
  exact f.adjoint_adjoint, fun h ↦ by
  obtain ⟨h, hσ⟩ := by simpa only [Set.mem_diff, Set.mem_singleton_iff] using h
  obtain ⟨h1, h2⟩ := f.adjoint.mem_range_singularValuesFin' hn σ |>.1 h
  refine ⟨f.mem_range_singularValuesFin' hn σ |>.2 ⟨f.adjoin_comp_eigenval_iff hn
    (by grind : σ ^ 2 ≠ 0)|>.2 ?_, h2⟩, by simpa⟩
  convert h1; exact f.adjoint_adjoint.symm⟩

lemma _root_.LinearIsometryEquiv.adjoint_eq_symm' (f : E ≃ₗᵢ[𝕜] F) :
    LinearMap.adjoint f.toLinearEquiv = f.symm.toLinearMap :=
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  f.toLinearEquiv.adjoint_eq_toCLM_adjoint ▸ congr($(LinearIsometryEquiv.adjoint_eq_symm f))

lemma singularValuesFin'_comp_linearIsometryEquiv {T : E →ₗ[𝕜] F} {f : E ≃ₗᵢ[𝕜] E} :
    (T ∘ₗ f.toLinearEquiv).singularValuesFin' hn = T.singularValuesFin' hn := by
  ext i
  simp only [singularValuesFin'_def]
  convert congr(Real.sqrt $(congr($((
    T.isPositive_adjoint_comp_self.1.eigenvlaues_linearIsometryEquiv_conj hn hn f.symm).symm) i)))
  simp only [adjoint_comp, LinearIsometryEquiv.toLinearEquiv_symm, LinearIsometryEquiv.symm_symm]
  rw [comp_assoc]
  congr
  exact LinearIsometryEquiv.adjoint_eq_symm' f
