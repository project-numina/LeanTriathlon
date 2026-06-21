/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.AdjointAction.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.JordanChevalley
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Lagrange

@[expose] public section

@[expose] public section

open LinearMap Module.End

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

namespace HumphreysLemma

omit [CharZero K] in
open Classical in

theorem eigenspaceIsInternal
    (s : Module.End K V) (hs : s.IsSemisimple) :
    DirectSum.IsInternal (fun μ : K => s.eigenspace μ) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  exact ⟨s.eigenspaces_iSupIndep, by
    have := iSup_maxGenEigenspace_eq_top s
    simp_rw [hs.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at this
    exact this⟩

omit [CharZero K] in
open Classical in

noncomputable def eigenbasis (s : Module.End K V) (hs : s.IsSemisimple) :=
  (eigenspaceIsInternal s hs).collectedBasis
    (fun μ => Module.finBasis K (s.eigenspace μ))

omit [CharZero K] in
open Classical in

-- `hs : s.IsSemisimple` cannot be inferred, so this is only ever applied explicitly
-- (see `eigenbasisFintype s hs_ss` below); the `impossibleInstance` linter is expected.
@[nolint impossibleInstance]
noncomputable instance eigenbasisFintype (s : Module.End K V) (hs : s.IsSemisimple) :
    Fintype (Σ μ : K, Fin (Module.finrank K (s.eigenspace μ))) :=
  Module.Basis.fintypeIndexOfRankLtAleph0 (eigenbasis s hs)
    (Module.rank_lt_aleph0 K V)

omit [CharZero K] in
open Classical in

theorem eigenbasis_eigenvalue (s : Module.End K V) (hs : s.IsSemisimple)
    (σ : Σ μ : K, Fin (Module.finrank K (s.eigenspace μ))) :
    s (eigenbasis s hs σ) = σ.1 • eigenbasis s hs σ := by
  have hmem := (eigenspaceIsInternal s hs).collectedBasis_mem
    (fun μ => Module.finBasis K (s.eigenspace μ)) σ
  exact mem_eigenspace_iff.mp hmem

omit [IsAlgClosed K] [CharZero K] [FiniteDimensional K V] in

noncomputable def eij {ι : Type*}
    (b : Module.Basis ι K V) (i j : ι) : Module.End K V :=
  (b.coord j).smulRight (b i)

omit [IsAlgClosed K] [CharZero K] [FiniteDimensional K V] in

theorem ad_diag_eij {ι : Type*}
    (b : Module.Basis ι K V) (a : ι → K) (s : Module.End K V)
    (hs : ∀ k, s (b k) = a k • b k)
    (i j : ι) : ⁅s, eij b i j⁆ = (a i - a j) • eij b i j := by
  classical
  apply b.ext; intro k
  change s (eij b i j (b k)) - eij b i j (s (b k)) =
    (a i - a j) • eij b i j (b k)
  simp only [eij, LinearMap.smulRight_apply, Module.Basis.coord_apply, hs k,
    map_smul, Module.Basis.repr_self]
  by_cases hjk : k = j
  · subst hjk
    simp only [Finsupp.single_eq_same, one_smul, hs i, sub_smul]
  · simp only [Finsupp.single_apply, hjk, ↓reduceIte, zero_smul, smul_zero,
      sub_self]

omit [IsAlgClosed K] [CharZero K] [FiniteDimensional K V] in

noncomputable def diagEnd {ι : Type*}
    (b : Module.Basis ι K V) (c : ι → K) : Module.End K V :=
  b.constr K (fun i => c i • b i)

omit [IsAlgClosed K] [CharZero K] [FiniteDimensional K V] in
theorem diagEnd_apply_basis {ι : Type*}
    (b : Module.Basis ι K V) (c : ι → K) (k : ι) :
    diagEnd b c (b k) = c k • b k := by
  simp [diagEnd, Module.Basis.constr_basis]

omit [IsAlgClosed K] [CharZero K] [FiniteDimensional K V] in

theorem ad_diagEnd_eij {ι : Type*}
    (b : Module.Basis ι K V) (c : ι → K) (i j : ι) :
    ⁅diagEnd b c, eij b i j⁆ = (c i - c j) • eij b i j :=
  ad_diag_eij b c (diagEnd b c) (diagEnd_apply_basis b c) i j

omit [IsAlgClosed K] [CharZero K] [FiniteDimensional K V] in

theorem toMatrix_diagEnd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (c : ι → K) :
    LinearMap.toMatrix b b (diagEnd b c) = Matrix.diagonal c := by
  ext i j
  rw [LinearMap.toMatrix_apply, diagEnd_apply_basis]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
    Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp [Finsupp.single_eq_same]
  · simp [h]

omit [IsAlgClosed K] [CharZero K] [FiniteDimensional K V] in

theorem trace_diagEnd {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K V) (c : ι → K) :
    trace K V (diagEnd b c) = ∑ i, c i := by
  classical
  rw [trace_eq_matrix_trace K b, toMatrix_diagEnd, Matrix.trace_diagonal]

omit [IsAlgClosed K] [CharZero K] [FiniteDimensional K V] in
open Classical in

noncomputable def eijBasis {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K V) : Module.Basis (ι × ι) K (Module.End K V) :=
  (Matrix.stdBasis K ι ι).map (LinearMap.toMatrix b b).symm

omit [IsAlgClosed K] [CharZero K] [FiniteDimensional K V] in
open Classical in

theorem eijBasis_eq {ι : Type*} [Fintype ι]
    (b : Module.Basis ι K V) (i j : ι) :
    eijBasis b (i, j) = eij b i j := by
  apply b.ext; intro k
  simp only [eijBasis, eij, Module.Basis.map_apply, LinearMap.smulRight_apply,
    Module.Basis.coord_apply, Matrix.stdBasis_eq_single]
  change (Matrix.toLin b b (Matrix.single i j 1)) (b k) = _
  rw [Matrix.toLin_self]
  simp only [Matrix.single_apply, Module.Basis.repr_self, Finsupp.single_apply]
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [hjk, eq_comm]

omit [IsAlgClosed K] [CharZero K] [FiniteDimensional K V] in

abbrev M (A B : Submodule K (Module.End K V)) : Set (Module.End K V) :=
  {x | ∀ b ∈ B, ⁅x, b⁆ ∈ A}

omit [IsAlgClosed K] [CharZero K] [FiniteDimensional K V] in

lemma aeval_ad_maps_to
    (A B : Submodule K (Module.End K V)) (hAB : A ≤ B)
    (x : Module.End K V) (hxM : ∀ b ∈ B, ⁅x, b⁆ ∈ A)
    (q : Polynomial K) (hq : Polynomial.eval 0 q = 0) :
    ∀ b ∈ B, (Polynomial.aeval (LieAlgebra.ad K (Module.End K V) x) q) b ∈ A := by
  set ad_x := LieAlgebra.ad K (Module.End K V) x
  have hdvd : Polynomial.X ∣ q := by
    have h := Polynomial.dvd_iff_isRoot.mpr (show q.IsRoot 0 from hq)
    simpa using h
  obtain ⟨q', rfl⟩ := hdvd
  have had_B : ∀ b ∈ B, ad_x b ∈ B := fun b hb => hAB (hxM b hb)
  have hpow_B : ∀ (n : ℕ) (b : Module.End K V), b ∈ B → (ad_x ^ n) b ∈ B := by
    intro n; induction n with
    | zero => intro b hb; simpa using hb
    | succ n ih => intro b hb; rw [pow_succ', Module.End.mul_apply]; exact had_B _ (ih b hb)
  have hpoly_B : ∀ (p : Polynomial K) (b : Module.End K V), b ∈ B →
      (Polynomial.aeval ad_x p) b ∈ B := by
    intro p; induction p using Polynomial.induction_on' with
    | add p q ihp ihq =>
      intro b hb; simp only [map_add, LinearMap.add_apply]; exact B.add_mem (ihp b hb) (ihq b hb)
    | monomial n c =>
      intro b hb
      simp only [Polynomial.aeval_monomial, Algebra.smul_def, Module.End.mul_apply,
        Module.algebraMap_end_apply]
      exact B.smul_mem c (hpow_B n b hb)
  intro b hb
  rw [map_mul, Polynomial.aeval_X, Module.End.mul_apply]
  exact hxM _ (hpoly_B q' b hb)

omit [IsAlgClosed K] [FiniteDimensional K V] in

theorem jordanChevalley_unique
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {f n₁ s₁ n₂ s₂ : Module.End K W}
    (hn₁ : IsNilpotent n₁) (hs₁ : s₁.IsSemisimple)
    (hn₂ : IsNilpotent n₂) (hs₂ : s₂.IsSemisimple)
    (hc₁ : Commute n₁ s₁) (hc₂ : Commute n₂ s₂)
    (h₁ : f = n₁ + s₁) (h₂ : f = n₂ + s₂) :
    n₁ = n₂ ∧ s₁ = s₂ := by
  have : PerfectField K := inferInstance

  obtain ⟨n_c, hn_c_adj, s_c, hs_c_adj, hn_c_nil, hs_c_ss, h_c⟩ :=
    f.exists_isNilpotent_isSemisimple

  have hc₁f : Commute s₁ f := h₁ ▸ hc₁.symm.add_right (Commute.refl s₁)
  have hc₂f : Commute s₂ f := h₂ ▸ hc₂.symm.add_right (Commute.refl s₂)
  have hn₁f : Commute n₁ f := h₁ ▸ (Commute.refl n₁).add_right hc₁
  have hn₂f : Commute n₂ f := h₂ ▸ (Commute.refl n₂).add_right hc₂

  have hcs₁ : Commute s₁ s_c :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hs_c_adj hc₁f
  have hcn₁ : Commute n₁ n_c :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hn_c_adj hn₁f
  have hcs₂ : Commute s₂ s_c :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hs_c_adj hc₂f
  have hcn₂ : Commute n₂ n_c :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hn_c_adj hn₂f

  have heq₁ : s₁ - s_c = n_c - n₁ := by
    have h := h₁.symm.trans h_c
    have : s₁ = n_c + s_c - n₁ := by rw [← h]; abel
    rw [this]; abel
  have h_s₁ : s₁ = s_c := by
    have hnil : IsNilpotent (s₁ - s_c) := heq₁ ▸ hcn₁.symm.isNilpotent_sub hn_c_nil hn₁
    have hss : (s₁ - s_c).IsSemisimple := hs₁.sub_of_commute hcs₁ hs_c_ss
    exact sub_eq_zero.mp (Module.End.eq_zero_of_isNilpotent_isSemisimple hnil hss)
  have heq₂ : s₂ - s_c = n_c - n₂ := by
    have h := h₂.symm.trans h_c
    have : s₂ = n_c + s_c - n₂ := by rw [← h]; abel
    rw [this]; abel
  have h_s₂ : s₂ = s_c := by
    have hnil : IsNilpotent (s₂ - s_c) := heq₂ ▸ hcn₂.symm.isNilpotent_sub hn_c_nil hn₂
    have hss : (s₂ - s_c).IsSemisimple := hs₂.sub_of_commute hcs₂ hs_c_ss
    exact sub_eq_zero.mp (Module.End.eq_zero_of_isNilpotent_isSemisimple hnil hss)
  constructor
  · rw [h_s₁] at h₁; rw [h_s₂] at h₂; exact add_right_cancel (h₁.symm.trans h₂)
  · exact h_s₁.trans h_s₂.symm

omit [IsAlgClosed K] [CharZero K] [FiniteDimensional K V] in

theorem commute_ad_of_commute {R : Type*} [CommRing R]
    {A : Type*} [Ring A] [Algebra R A] {a b : A}
    (h : Commute a b) :
    Commute (LieAlgebra.ad R A a) (LieAlgebra.ad R A b) := by
  rw [Commute, SemiconjBy, ← sub_eq_zero, ← Ring.lie_def,
      ← (LieAlgebra.ad R A).map_lie, Ring.lie_def, sub_eq_zero.mpr h, map_zero]

open Polynomial in
omit [IsAlgClosed K] [CharZero K] [FiniteDimensional K V] in
private lemma aeval_mulRight_apply (a : Module.End K V) (p : K[X]) (T : Module.End K V) :
    (aeval (mulRight K a) p) T = T * aeval a p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq, mul_add]
  | monomial n c =>
    simp only [aeval_monomial, ← Algebra.smul_def, LinearMap.smul_apply,
        mul_smul_comm, pow_mulRight, mulRight_apply]

open Polynomial in
omit [IsAlgClosed K] [CharZero K] in
private theorem isSemisimple_mulLeft_of_isSemisimple
    {a : Module.End K V} (ha : a.IsSemisimple) :
    IsSemisimple (mulLeft K a) := by
  apply isSemisimple_of_squarefree_aeval_eq_zero ha.minpoly_squarefree
  have : aeval (Algebra.lmul K (Module.End K V) a) (minpoly K a) = 0 := by
    rw [aeval_algHom_apply, minpoly.aeval, map_zero]
  simpa using this

omit [IsAlgClosed K] [CharZero K] in
private theorem isSemisimple_mulRight_of_isSemisimple
    {a : Module.End K V} (ha : a.IsSemisimple) :
    IsSemisimple (mulRight K a) := by
  apply isSemisimple_of_squarefree_aeval_eq_zero ha.minpoly_squarefree
  ext1 T
  simp only [LinearMap.zero_apply, aeval_mulRight_apply, minpoly.aeval, mul_zero]

omit [IsAlgClosed K] [CharZero K] in

theorem ad_isSemisimple_of_isSemisimple [PerfectField K]
    {a : Module.End K V} (ha : a.IsSemisimple) :
    (LieAlgebra.ad K (Module.End K V) a).IsSemisimple := by
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  exact (isSemisimple_mulLeft_of_isSemisimple ha).sub_of_commute
    (LinearMap.commute_mulLeft_right a a)
    (isSemisimple_mulRight_of_isSemisimple ha)

omit [IsAlgClosed K] in

lemma ad_semisimple_part
    (x n s : Module.End K V)
    (hn_nil : IsNilpotent n) (hs_ss : s.IsSemisimple)
    (hxns : x = n + s) :
    LieAlgebra.ad K (Module.End K V) x =
      LieAlgebra.ad K (Module.End K V) n + LieAlgebra.ad K (Module.End K V) s ∧
    IsNilpotent (LieAlgebra.ad K (Module.End K V) n) ∧
    (LieAlgebra.ad K (Module.End K V) s).IsSemisimple := by
  have : PerfectField K := inferInstance
  have : FiniteDimensional K (Module.End K V) := inferInstance
  exact ⟨by rw [hxns, map_add],
         LieAlgebra.ad_nilpotent_of_nilpotent hn_nil,
         ad_isSemisimple_of_isSemisimple hs_ss⟩

omit [IsAlgClosed K] in

lemma ad_semisimple_part_in_adjoin
    (x n s : Module.End K V)
    (hn_adj : n ∈ Algebra.adjoin K {x})
    (hs_adj : s ∈ Algebra.adjoin K {x})
    (hn_nil : IsNilpotent n) (hs_ss : s.IsSemisimple)
    (hxns : x = n + s) :
    LieAlgebra.ad K (Module.End K V) s ∈
      Algebra.adjoin K {LieAlgebra.ad K (Module.End K V) x} := by
  have : PerfectField K := inferInstance
  have : FiniteDimensional K (Module.End K V) := inferInstance
  set ad := LieAlgebra.ad K (Module.End K V)

  obtain ⟨h_sum, h_ad_n_nil, h_ad_s_ss⟩ := ad_semisimple_part x n s hn_nil hs_ss hxns

  have hc_xn : Commute x n := Algebra.commute_of_mem_adjoin_self hn_adj
  have hc_ns : Commute n s :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hs_adj hc_xn.symm

  obtain ⟨n', hn'_adj, s', hs'_adj, hn'_nil, hs'_ss, h_jc⟩ :=
    (ad x).exists_isNilpotent_isSemisimple
  have hc_n' : Commute (ad x) n' := Algebra.commute_of_mem_adjoin_self hn'_adj
  have hc_s' : Commute (ad x) s' := Algebra.commute_of_mem_adjoin_self hs'_adj
  have hc_canonical : Commute n' s' :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hs'_adj hc_n'.symm
  have hc_ad : Commute (ad n) (ad s) := commute_ad_of_commute hc_ns

  exact (jordanChevalley_unique hn'_nil hs'_ss h_ad_n_nil h_ad_s_ss
    hc_canonical hc_ad h_jc h_sum).2 ▸ hs'_adj

omit [IsAlgClosed K] [CharZero K] [FiniteDimensional K V] in

theorem aeval_apply_of_eigenvalue {R : Type*} {M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M]
    {f : Module.End R M} {μ : R} {x : M} (hx : f x = μ • x) (p : Polynomial R) :
    (Polynomial.aeval f p) x = (Polynomial.eval μ p) • x := by
  refine p.induction_on ?_ ?_ ?_
  · intro a; simp [Module.algebraMap_end_apply]
  · intro p q hp hq; simp [hp, hq, add_smul]
  · intro n a hna
    rw [mul_comm, pow_succ', mul_assoc, map_mul, Module.End.mul_apply, mul_comm, hna]
    simp only [hx, smul_smul, Polynomial.aeval_X, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, map_smulₛₗ, RingHom.id_apply, mul_comm]

omit [IsAlgClosed K] in

lemma ad_semisimple_part_polynomial
    (x n s : Module.End K V)
    (hn_adj : n ∈ Algebra.adjoin K {x})
    (hs_adj : s ∈ Algebra.adjoin K {x})
    (hn_nil : IsNilpotent n) (hs_ss : s.IsSemisimple)
    (hxns : x = n + s) :
    ∃ p : Polynomial K, Polynomial.eval 0 p = 0 ∧
      LieAlgebra.ad K (Module.End K V) s =
        Polynomial.aeval (LieAlgebra.ad K (Module.End K V) x) p := by
  set ad := LieAlgebra.ad K (Module.End K V)

  have h_mem := ad_semisimple_part_in_adjoin x n s hn_adj hs_adj hn_nil hs_ss hxns
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h_mem
  obtain ⟨q, hq⟩ := h_mem

  have had_x_x : (ad x) x = 0 := by
    change ⁅x, x⁆ = 0; exact lie_self x
  have had_s_x : (ad s) x = 0 := by
    change ⁅s, x⁆ = 0
    have : Commute x s := Algebra.commute_of_mem_adjoin_self hs_adj
    have e := Ring.lie_def s x
    rw [this.eq, sub_self] at e
    rw [← e]
    rfl

  have hq' : ad s = Polynomial.aeval (ad x) q := hq.symm
  have h_eval : (Polynomial.aeval (ad x) q) x = Polynomial.eval 0 q • x :=
    aeval_apply_of_eigenvalue (by rw [zero_smul]; exact had_x_x) q
  rw [← hq'] at h_eval
  rw [had_s_x] at h_eval

  by_cases hx : x = 0
  ·
    have h0 : n + s = 0 := by rw [← hxns]; exact hx
    have hs0 : s = 0 := by
      have : IsNilpotent s := by
        have hs_neg : s = -n := by
          have : s = -n + (n + s) := by abel
          rw [h0, add_zero] at this; exact this
        rw [hs_neg]; exact hn_nil.neg
      exact Module.End.eq_zero_of_isNilpotent_isSemisimple this hs_ss
    exact ⟨0, by simp, by simp [hs0, map_zero]⟩
  ·
    have hq0 : Polynomial.eval 0 q = 0 := by
      by_contra h
      exact hx (smul_eq_zero.mp h_eval.symm |>.resolve_left h)
    exact ⟨q, hq0, hq'⟩

omit [CharZero K] in

lemma eq_zero_of_isSemisimple_of_forall_eigenvalue_eq_zero
    (s : Module.End K V) (hs : s.IsSemisimple)
    (h : ∀ μ : K, s.HasEigenvalue μ → μ = 0) : s = 0 := by
  have h_top : ⨆ μ, s.maxGenEigenspace μ = ⊤ := iSup_maxGenEigenspace_eq_top s
  have h_eq : ∀ μ, s.maxGenEigenspace μ = s.eigenspace μ :=
    hs.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace
  simp_rw [h_eq] at h_top
  have h_bot : ∀ μ ≠ (0 : K), s.eigenspace μ = ⊥ := by
    intro μ hμ
    by_contra h_ne
    exact hμ (h μ (hasEigenvalue_iff.mpr h_ne))
  have h_ker : s.eigenspace 0 = ⊤ := by
    rw [← h_top]
    apply le_antisymm (le_iSup _ 0)
    apply iSup_le; intro μ
    rcases eq_or_ne μ 0 with rfl | hμ
    · exact le_refl _
    · rw [h_bot μ hμ]; exact bot_le
  rw [eigenspace_zero] at h_ker
  exact ker_eq_top.mp h_ker

omit [IsAlgClosed K] in

lemma exists_lagrange_polynomial
    {ι : Type*} [Finite ι]
    (a : ι → K) (E : Submodule ℚ K) (f : E →ₗ[ℚ] ℚ)
    (ha : ∀ i, a i ∈ E) :
    ∃ r : Polynomial K,
      (∀ i j, Polynomial.eval (a i - a j) r =
        algebraMap ℚ K (f ⟨a i, ha i⟩) - algebraMap ℚ K (f ⟨a j, ha j⟩)) ∧
      Polynomial.eval 0 r = 0 := by
  classical
  have : Fintype ι := Fintype.ofFinite ι

  let diffs : Finset K := Finset.univ.image (fun p : ι × ι => a p.1 - a p.2)
  have ha_diff : ∀ i j, a i - a j ∈ E := fun i j => E.sub_mem (ha i) (ha j)

  let g : K → K := fun d => if hd : d ∈ E then algebraMap ℚ K (f ⟨d, hd⟩) else 0
  let v : K → K := fun x => x
  refine ⟨Lagrange.interpolate diffs v g, fun i j => ?_, ?_⟩
  ·
    have h_mem : a i - a j ∈ diffs :=
      Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩
    rw [Lagrange.eval_interpolate_at_node g (fun _ _ _ _ h => h) h_mem,
      show g (a i - a j) = algebraMap ℚ K (f ⟨a i - a j, ha_diff i j⟩) from
        dif_pos (ha_diff i j)]
    have : (⟨a i - a j, ha_diff i j⟩ : E) = ⟨a i, ha i⟩ - ⟨a j, ha j⟩ := rfl
    rw [this, map_sub, map_sub]
  ·
    by_cases h_ne : Nonempty ι
    · obtain ⟨i⟩ := h_ne
      have h_mem : (0 : K) ∈ diffs :=
        Finset.mem_image.mpr ⟨(i, i), Finset.mem_univ _, sub_self _⟩
      rw [Lagrange.eval_interpolate_at_node g (fun _ _ _ _ h => h) h_mem,
        show g 0 = algebraMap ℚ K (f ⟨0, E.zero_mem⟩) from dif_pos E.zero_mem]
      have : (⟨(0 : K), E.zero_mem⟩ : E) = 0 := rfl
      rw [this, map_zero, map_zero]
    · rw [not_nonempty_iff] at h_ne
      have h_empty : diffs = ∅ := by
        simp only [diffs, Finset.image_eq_empty]; exact Finset.univ_eq_empty
      simp [Lagrange.interpolate_apply, h_empty]

end HumphreysLemma

open HumphreysLemma in

theorem humphreys_lemma_algClosed
    (A B : Submodule K (Module.End K V))
    (hAB : A ≤ B)
    (x : Module.End K V)
    (hxM : x ∈ M A B)
    (htr : ∀ y ∈ M A B, trace K V (x * y) = 0) :
    IsNilpotent x := by

  obtain ⟨n, hn_adj, s, hs_adj, hn_nil, hs_ss, hxns⟩ :=
    x.exists_isNilpotent_isSemisimple

  let v := eigenbasis s hs_ss
  let a : (Σ μ : K, Fin (Module.finrank K (s.eigenspace μ))) → K := fun i => i.1
  have hv_diag : ∀ i, s (v i) = a i • v i := eigenbasis_eigenvalue s hs_ss

  let E : Submodule ℚ K := Submodule.span ℚ (Set.range a)

  suffices hs_zero : s = 0 by rw [hxns, hs_zero, add_zero]; exact hn_nil

  suffices h_f_zero : ∀ f : E →ₗ[ℚ] ℚ, f = 0 by

    apply eq_zero_of_isSemisimple_of_forall_eigenvalue_eq_zero s hs_ss
    intro μ hμ

    have hpos : 0 < Module.finrank K (s.eigenspace μ) := by
      have : Nontrivial (s.eigenspace μ) :=
        Submodule.nontrivial_iff_ne_bot.mpr (hasEigenvalue_iff.mp hμ)
      exact Module.finrank_pos
    have hμ_E : μ ∈ E := Submodule.subset_span ⟨⟨μ, ⟨0, hpos⟩⟩, rfl⟩

    have hμ_zero : (⟨μ, hμ_E⟩ : E) = 0 :=
      (Module.forall_dual_apply_eq_zero_iff ℚ _).mp (fun φ => by simp [h_f_zero φ])
    exact congr_arg Subtype.val hμ_zero

  intro f

  have ha : ∀ i, a i ∈ E := fun i => Submodule.subset_span (Set.mem_range_self i)

  let y := diagEnd v (fun i => algebraMap ℚ K (f ⟨a i, ha i⟩))

  have had_s : ∀ i j, ⁅s, eij v i j⁆ = (a i - a j) • eij v i j :=
    ad_diag_eij v a s hv_diag

  have had_y : ∀ i j, ⁅y, eij v i j⁆ =
      (algebraMap ℚ K (f ⟨a i, ha i⟩) - algebraMap ℚ K (f ⟨a j, ha j⟩)) •
        eij v i j :=
    fun i j => ad_diagEnd_eij v _ i j

  have : Fintype (Σ μ : K, Fin (Module.finrank K (s.eigenspace μ))) :=
    eigenbasisFintype s hs_ss
  obtain ⟨r, hr_eval, hr_zero⟩ := exists_lagrange_polynomial a E f ha

  let ad_s := LieAlgebra.ad K (Module.End K V) s
  have had_y_eq : LieAlgebra.ad K (Module.End K V) y = Polynomial.aeval ad_s r := by
    apply (eijBasis v).ext; intro ⟨i, j⟩
    rw [eijBasis_eq]
    change ⁅y, eij v i j⁆ = (Polynomial.aeval ad_s r) (eij v i j)
    rw [aeval_apply_of_eigenvalue (had_s i j) r, hr_eval i j, had_y i j]

  obtain ⟨p, hp_zero, hp_eq⟩ :=
    ad_semisimple_part_polynomial x n s hn_adj hs_adj hn_nil hs_ss hxns

  let ad_x := LieAlgebra.ad K (Module.End K V) x
  have had_y_adx : LieAlgebra.ad K (Module.End K V) y =
      Polynomial.aeval ad_x (r.comp p) := by
    rw [had_y_eq]
    have : ad_s = Polynomial.aeval ad_x p := hp_eq
    rw [this, ← Polynomial.aeval_comp]
  have hcomp_zero : Polynomial.eval 0 (r.comp p) = 0 := by
    simp [Polynomial.eval_comp, hp_zero, hr_zero]

  have hyM : y ∈ M A B := by
    intro b hb
    change (LieAlgebra.ad K (Module.End K V) y) b ∈ A
    rw [had_y_adx]
    exact aeval_ad_maps_to A B hAB x hxM (r.comp p) hcomp_zero b hb

  have htr_xy : trace K V (x * y) = 0 := htr y hyM

  have htr_sum : ∑ i : (Σ μ : K, Fin (Module.finrank K (s.eigenspace μ))),
      a i * algebraMap ℚ K (f ⟨a i, ha i⟩) = 0 := by
    classical

    let eigenvals : Finset K := Finset.univ.image a
    let c_val : K → K := fun μ => if hμ : μ ∈ E then algebraMap ℚ K (f ⟨μ, hμ⟩) else 0
    let g := Lagrange.interpolate eigenvals id c_val
    have hg_eval : ∀ i, Polynomial.eval (a i) g = algebraMap ℚ K (f ⟨a i, ha i⟩) := by
      intro i
      have h_mem : a i ∈ eigenvals := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      exact (Lagrange.eval_interpolate_at_node c_val
        (fun _ _ _ _ h => h) h_mem).trans (dif_pos (ha i))

    have hy_eq : Polynomial.aeval s g = y := by
      apply v.ext; intro i
      rw [aeval_apply_of_eigenvalue (hv_diag i) g, hg_eval i, diagEnd_apply_basis]

    have hy_adj_s : y ∈ Algebra.adjoin K {s} := by
      rw [Algebra.adjoin_singleton_eq_range_aeval]
      exact ⟨g, hy_eq⟩

    have hy_adj_x : y ∈ Algebra.adjoin K {x} :=
      Algebra.adjoin_singleton_le hs_adj hy_adj_s

    have hc_nx : Commute n x := (Algebra.commute_of_mem_adjoin_self hn_adj).symm
    have hcommute_ny : Commute n y :=
      Algebra.commute_of_mem_adjoin_singleton_of_commute hy_adj_x hc_nx

    have htr_ny : trace K V (n * y) = 0 := by
      have h_nil : IsNilpotent (n * y) := hcommute_ny.isNilpotent_mul_right hn_nil
      exact (LinearMap.isNilpotent_trace_of_isNilpotent h_nil).eq_zero

    have hsy_diag : s * y =
        diagEnd v (fun i => a i * algebraMap ℚ K (f ⟨a i, ha i⟩)) := by
      apply v.ext; intro i
      change s (y (v i)) = _
      rw [show y (v i) = algebraMap ℚ K (f ⟨a i, ha i⟩) • v i from diagEnd_apply_basis v _ i,
        diagEnd_apply_basis, map_smul, hv_diag i, smul_smul, mul_comm]

    have htr_sy : trace K V (s * y) =
        ∑ i, a i * algebraMap ℚ K (f ⟨a i, ha i⟩) :=
      hsy_diag ▸ trace_diagEnd v _

    have htr_split : trace K V (x * y) =
        trace K V (n * y) + trace K V (s * y) := by
      conv_lhs => rw [hxns, add_mul]
      exact map_add (trace K V) (n * y) (s * y)

    rw [← htr_sy]
    have h := htr_split.symm.trans htr_xy
    rw [htr_ny, zero_add] at h
    exact h

  have h_sum_E : ∑ i : (Σ μ : K, Fin (Module.finrank K (s.eigenspace μ))),
      (f ⟨a i, ha i⟩) • (⟨a i, ha i⟩ : E) = 0 := by

    apply_fun E.subtype using Subtype.val_injective
    simp only [map_sum, map_smul, map_zero, Submodule.subtype_apply]

    convert htr_sum using 1
    congr 1; ext i
    rw [Algebra.smul_def, mul_comm]

  have h_sum_sq : ∑ i : (Σ μ : K, Fin (Module.finrank K (s.eigenspace μ))),
      f ⟨a i, ha i⟩ ^ 2 = (0 : ℚ) := by
    have := congr_arg f h_sum_E
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at this
    convert this using 1
    congr 1; ext i; ring

  have h_f_zero_all : ∀ i, f ⟨a i, ha i⟩ = 0 := by
    intro i
    have h_nonneg : ∀ j ∈ Finset.univ,
        (0 : ℚ) ≤ (fun j => f ⟨a j, ha j⟩ ^ 2) j := fun j _ => sq_nonneg _
    have := (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h_sum_sq i (Finset.mem_univ _)
    exact eq_zero_of_pow_eq_zero this

  ext ⟨e, he⟩
  simp only [LinearMap.zero_apply]
  refine Submodule.span_induction
    (p := fun e he => f ⟨e, he⟩ = 0)
    (fun k hk => ?_) (map_zero f) (fun x y hx hy ihx ihy => ?_)
    (fun q x hx ih => ?_) he
  · obtain ⟨i, rfl⟩ := hk
    exact h_f_zero_all i
  · change f (⟨x, hx⟩ + ⟨y, hy⟩) = 0
    rw [map_add, ihx, ihy, add_zero]
  · change f (q • ⟨x, hx⟩) = 0
    rw [map_smul, ih, smul_zero]
