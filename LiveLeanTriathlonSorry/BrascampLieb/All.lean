/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib.LinearAlgebra.FreeModule.Determinant
import Mathlib.Tactic.Attr.Register
public import Mathlib.Analysis.Matrix.LDL
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import LiveLeanTriathlonSorry.Mathlib.Analysis.Normed.Operator.LinearIsometry
public import LiveLeanTriathlonSorry.Util.Attributes
public import LiveLeanTriathlonSorry.Mathlib.Analysis.InnerProductSpace.PosDef
public import LiveLeanTriathlonSorry.Mathlib.Analysis.InnerProductSpace.SingularValue
public import LiveLeanTriathlonSorry.Mathlib.Analysis.InnerProductSpace.GramMatrix
public import LiveLeanTriathlonSorry.Mathlib.LinearAlgebra.Matrix.Hermitian
public import LiveLeanTriathlonSorry.Mathlib.Order.Interval.Finset.Defs
public import LiveLeanTriathlonSorry.Mathlib.Algebra.BigOperators.Fin
public import LiveLeanTriathlonSorry.Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import LiveLeanTriathlonSorry.Mathlib.Analysis.InnerProductSpace.PiL2
@[expose] public section

section Background

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] {n} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (hn : Module.finrank 𝕜 E = n) [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (α : NNReal) (l : E →ₗ[𝕜] F)

noncomputable def EssRankAux :=
  Finset.univ.filter (fun i ↦ (α : ℝ) < l.singularValuesFin' hn i)

noncomputable def EssentialRank : ℕ := Finset.card <| l.EssRankAux hn α

noncomputable def EssentialRankRestrict {m} (W : Submodule 𝕜 E)
    (hm : Module.finrank 𝕜 W = m) : ℕ :=
  (l.domRestrict W).EssentialRank hm α

end LinearMap

namespace BrascampLieb

structure Datum {J : Type*} [Fintype J]
    (E : Type*) [AddCommGroup E] [Module ℝ E]
    (F : J → Type*) [(i : J) → AddCommGroup (F i)] [(i : J) → Module ℝ (F i)]
  where
  map : (j : J) → E →ₗ[ℝ] (F j)
  weight : J → NNReal

noncomputable def Datum.AcuityWithin {J : Type*} [Fintype J] {E : Type*} {F : J → Type*} {m}
    [NormedAddCommGroup E] [(i : J) → NormedAddCommGroup (F i)]
    [InnerProductSpace ℝ E] [(i : J) → InnerProductSpace ℝ (F i)]
    [FiniteDimensional ℝ E] [(i : J) → FiniteDimensional ℝ (F i)]
    (D : Datum E F) (α : J → NNReal) (W : Submodule ℝ E) (hm : Module.finrank ℝ W = m) : NNReal :=
  ∑ j, D.weight j * (D.map j).EssentialRankRestrict (α j) W hm

noncomputable abbrev Datum.Acuity {J : Type*} [Fintype J]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {F : J → Type*} [(i : J) → AddCommGroup (F i)] [(i : J) → Module ℝ (F i)]
    (D : Datum E F) : NNReal :=
  ∑ j, D.weight j * Module.finrank ℝ (F j)

noncomputable def Datum.IsMetricPercep {J : Type*} [Fintype J] {E : Type*} {F : J → Type*}
    [NormedAddCommGroup E] [(i : J) → NormedAddCommGroup (F i)]
    [InnerProductSpace ℝ E] [(i : J) → InnerProductSpace ℝ (F i)]
    [FiniteDimensional ℝ E] [(i : J) → FiniteDimensional ℝ (F i)]
    (D : Datum E F) (α : J → NNReal) (β : NNReal) :=
  ∀ {m} (W : Submodule ℝ E) (hm : Module.finrank ℝ W = m),
    Module.finrank ℝ W ≤ D.AcuityWithin α W hm + β

structure locDatum {J : Type*} [Fintype J]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : J → Type*) [(j : J) → AddCommGroup (F j)] [(j : J) → Module ℝ (F j)]
  extends Datum E F where
  loc : E →ₗ[ℝ] E
  pos_loc : LinearMap.IsPosDef loc

structure locRegDatum {J : Type*} [Fintype J]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : J → Type*) [(j : J) → NormedAddCommGroup (F j)] [(j : J) → InnerProductSpace ℝ (F j)]
  extends locDatum E F where
  reg : (j : J) → F j →ₗ[ℝ] F j
  pos_reg: (j : J) → LinearMap.IsPosDef (reg j)

lemma loc_c_PosDef {J : Type*} [Fintype J]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {F : J → Type*} [(j : J) → NormedAddCommGroup (F j)]
    [(j : J) → InnerProductSpace ℝ (F j)] [(j : J) → FiniteDimensional ℝ (F j)]
    (D : locDatum E F) (A : (j : J) → (F j) →ₗ[ℝ] (F j))
    (hA : (j : J) → LinearMap.IsPosDef (A j)) :
    (D.loc + ∑ j, (D.weight j : ℝ) • ((D.map j).adjoint ∘ₗ A j ∘ₗ D.map j)).IsPosDef := sorry

noncomputable abbrev loc_constant_g_of {J : Type*} [Fintype J]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {F : J → Type*} [(j : J) → NormedAddCommGroup (F j)]
    [(j : J) → InnerProductSpace ℝ (F j)] [(j : J) → FiniteDimensional ℝ (F j)]
    (D : locDatum E F) (A : (j : J) → (F j) →ₗ[ℝ] (F j))
    (hA : (j : J) → LinearMap.IsPosDef (A j)) : NNReal :=
  NNReal.sqrt ((∏ j : J, ⟨(A j).det, by classical exact (hA j).1.det_nonneg⟩ ^ (D.weight j : ℝ)) /
    ⟨LinearMap.det <| D.loc + ∑ j, (D.weight j : ℝ) • ((D.map j).adjoint ∘ₗ A j ∘ₗ D.map j),
    (loc_c_PosDef D A hA).det_pos.le⟩)

noncomputable abbrev loc_reg_constant_g {J : Type*} [Fintype J] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {F : J → Type*}
    [(j : J) → NormedAddCommGroup (F j)] [(j : J) → InnerProductSpace ℝ (F j)]
    [(j : J) → FiniteDimensional ℝ (F j)] (D : locRegDatum E F) : ENNReal :=
  iSup <| fun A : {A : (j : J) → F j →ₗ[ℝ] F j // ∀ j,
    LinearMap.IsPosDef (A j) ∧ A j ≤ D.reg j } ↦
    loc_constant_g_of D.tolocDatum A (fun j ↦ (A.prop j).1)

end BrascampLieb

namespace BrascampLieb

variable {J E F : Type*} {n m} [Fintype J] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (hn : Module.finrank ℝ E = n) [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] (hm : Module.finrank ℝ F = m) [FiniteDimensional ℝ F] {α : NNReal}

open EuclideanSpace

-- Needed for def

omit [FiniteDimensional ℝ F] in
lemma greedy_index_set_exists {d : ℕ} (hα : 0 < α)
    (ℓ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] F) : ∃ I : Finset (Fin d),
    (∀ i ∈ I, Metric.infDist (ℓ (single i 1)) (ℓ '' Submodule.span ℝ (basisFun (Fin d) ℝ ''
      (I ∩ Finset.Ioi i))) ≥ α / NNReal.sqrt d) ∧ (∀ i, Metric.infDist (ℓ (single i (1 : ℝ)))
      (ℓ '' Submodule.span ℝ (basisFun (Fin d) ℝ '' (I ∩ Finset.Ici i))) < α / NNReal.sqrt d) := by sorry

omit [FiniteDimensional ℝ F] in
noncomputable def greedy_index_set {d : ℕ} (hα : 0 < α)
    (ℓ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] F) : Finset (Fin d) :=
  greedy_index_set_exists hα ℓ|>.choose

end BrascampLieb

end Background

section Main

namespace BrascampLieb

open EuclideanSpace in

@[AMS 26]
theorem upperBound {J E : Type*} [Fintype J] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {F : J → Type*} [(j : J) → NormedAddCommGroup (F j)]
    [(j : J) → InnerProductSpace ℝ (F j)] [(j : J) → FiniteDimensional ℝ (F j)]
    (hE : Module.finrank ℝ E ≠ 0)
    (D : locRegDatum E F) (α : J → NNReal) (β : NNReal) (hα : ∀ i, 0 < α i)
    (hP : D.IsMetricPercep α β)
    (hS : ∀ j : J, (D.map j).EssentialRank rfl (α j) = Module.finrank ℝ (F j)) :
    let M_max := (D.loc + ∑ j, (D.weight j) • (D.map j).adjoint ∘ₗ (D.reg j) ∘ₗ (D.map j))
    loc_reg_constant_g D ≤
      (Module.finrank ℝ E : NNReal)^(D.Acuity / 2 : ℝ) *
      (∏ j, (D.weight j)^(- (D.weight j : ℝ) * Module.finrank ℝ (F j) / 2)) *
      (∏ j, (α j)^(- (D.weight j : ℝ) * Module.finrank ℝ (F j))) *
      ‖M_max.toContinuousLinearMap‖₊^((D.Acuity.toReal - Module.finrank ℝ E + β) / 2) *
      ‖(D.loc.equivOfDetNeZero D.pos_loc.2).symm.toContinuousLinearMap‖₊^(β.toReal / 2) := by sorry

end BrascampLieb

end Main
