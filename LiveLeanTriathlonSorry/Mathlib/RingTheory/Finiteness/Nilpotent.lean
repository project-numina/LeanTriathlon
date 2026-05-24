/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib
public import LiveLeanTriathlonSorry.Mathlib.FieldTheory.IsAlgClosed.Basic
public import LiveLeanTriathlonSorry.Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib

@[expose] public section

private lemma isNilpotent_pow_sub_of_isNilpotent_sub_aux {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (g : M →ₗ[R] M) (c : R) (k : ℕ)
    (h : IsNilpotent (g - algebraMap R (M →ₗ[R] M) c)) :
    IsNilpotent (g ^ k - algebraMap R (M →ₗ[R] M) (c ^ k)) := by

  set n := g - algebraMap R (M →ₗ[R] M) c with hn_def
  have hg : g = algebraMap R (M →ₗ[R] M) c + n := by simp [hn_def]
  have hcomm : Commute (algebraMap R (M →ₗ[R] M) c) n := Algebra.commute_algebraMap_left c n
  rw [hg, hcomm.add_pow k]
  simp only [map_pow]
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one]
  rw [add_sub_cancel_right]
  apply Commute.isNilpotent_sum
  · intro i hi
    have hki : 1 ≤ k - i := by simp only [Finset.mem_range] at hi; omega
    have hcast : (↑(k.choose i) : M →ₗ[R] M) = (k.choose i) • (1 : M →ₗ[R] M) := by
      simp only [nsmul_eq_mul, mul_one]
    rw [hcast, mul_smul_one]
    apply IsNilpotent.smul
    have hcomm_pow : Commute (algebraMap R (M →ₗ[R] M) c ^ i) (n ^ (k - i)) :=
      (Algebra.commute_algebraMap_left c n).pow_pow i (k - i)
    apply hcomm_pow.isNilpotent_mul_left
    exact h.pow_of_pos (Nat.one_le_iff_ne_zero.mp hki)
  · intro i j _ _
    have hcast_i : (↑(k.choose i) : M →ₗ[R] M) = (k.choose i) • (1 : M →ₗ[R] M) := by
      simp only [nsmul_eq_mul, mul_one]
    have hcast_j : (↑(k.choose j) : M →ₗ[R] M) = (k.choose j) • (1 : M →ₗ[R] M) := by
      simp only [nsmul_eq_mul, mul_one]
    rw [hcast_i, hcast_j, mul_smul_one, mul_smul_one]
    apply Commute.smul_right
    apply Commute.smul_left
    have hc_n : Commute (algebraMap R (M →ₗ[R] M) c) n := Algebra.commute_algebraMap_left c n
    show (algebraMap R (M →ₗ[R] M) c ^ i * n ^ (k - i)) *
           (algebraMap R (M →ₗ[R] M) c ^ j * n ^ (k - j)) =
         (algebraMap R (M →ₗ[R] M) c ^ j * n ^ (k - j)) *
           (algebraMap R (M →ₗ[R] M) c ^ i * n ^ (k - i))
    have hc_pow_n_pow : ∀ a b : ℕ, Commute (algebraMap R (M →ₗ[R] M) c ^ a) (n ^ b) :=
      fun a b ↦ hc_n.pow_pow a b
    have hn_pow_comm : ∀ a b : ℕ, Commute (n ^ a) (n ^ b) := fun a b ↦ (Commute.refl n).pow_pow a b
    have hc_pow_comm : ∀ a b : ℕ,
        Commute (algebraMap R (M →ₗ[R] M) c ^ a) (algebraMap R (M →ₗ[R] M) c ^ b) :=
      fun a b ↦ (Commute.refl _).pow_pow a b
    simp only [← mul_assoc]
    have h1 : (algebraMap R (M →ₗ[R] M) c ^ i) * (n ^ (k - i)) *
              (algebraMap R (M →ₗ[R] M) c ^ j) * (n ^ (k - j)) =
              (algebraMap R (M →ₗ[R] M) c ^ i) * (algebraMap R (M →ₗ[R] M) c ^ j) *
              (n ^ (k - i)) * (n ^ (k - j)) := by
      rw [mul_assoc (algebraMap R (M →ₗ[R] M) c ^ i) (n ^ (k - i))]
      rw [(hc_pow_n_pow j (k - i)).symm.eq]
      simp only [mul_assoc]
    have h2 : (algebraMap R (M →ₗ[R] M) c ^ j) * (n ^ (k - j)) *
              (algebraMap R (M →ₗ[R] M) c ^ i) * (n ^ (k - i)) =
              (algebraMap R (M →ₗ[R] M) c ^ j) * (algebraMap R (M →ₗ[R] M) c ^ i) *
              (n ^ (k - j)) * (n ^ (k - i)) := by
      rw [mul_assoc (algebraMap R (M →ₗ[R] M) c ^ j) (n ^ (k - j))]
      rw [(hc_pow_n_pow i (k - j)).symm.eq]
      simp only [mul_assoc]
    rw [h1, h2, (hc_pow_comm i j).eq]
    simp only [mul_assoc]
    rw [(hn_pow_comm (k - i) (k - j)).eq]

private lemma trace_algebraMap_eq_finrank_smul_aux {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M] (c : R) :
    LinearMap.trace R M (algebraMap R (M →ₗ[R] M) c) = Module.finrank R M • c := by
  rw [Algebra.algebraMap_eq_smul_one, LinearMap.map_smul, LinearMap.trace_one,
      smul_eq_mul, mul_comm, ← nsmul_eq_mul]

private lemma trace_pow_eq_pow_smul_finrank_of_isNilpotent_sub_aux {R M : Type*}
    [CommRing R] [IsReduced R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M]
    (g : M →ₗ[R] M) (c : R) (k : ℕ)
    (h : IsNilpotent (g - algebraMap R (M →ₗ[R] M) c)) :
    LinearMap.trace R M (g ^ k) = Module.finrank R M • (c ^ k) := by
  have h_nil := isNilpotent_pow_sub_of_isNilpotent_sub_aux g c k h
  have h_trace_nil : LinearMap.trace R M (g ^ k - algebraMap R (M →ₗ[R] M) (c ^ k)) = 0 :=
    isNilpotent_iff_eq_zero.mp (LinearMap.isNilpotent_trace_of_isNilpotent h_nil)
  have h_linear : LinearMap.trace R M (g ^ k - algebraMap R (M →ₗ[R] M) (c ^ k)) =
      LinearMap.trace R M (g ^ k) - LinearMap.trace R M (algebraMap R (M →ₗ[R] M) (c ^ k)) := by
    rw [map_sub]
  rw [h_linear, trace_algebraMap_eq_finrank_smul_aux] at h_trace_nil
  simp only [sub_eq_zero] at h_trace_nil
  exact h_trace_nil

lemma LinearMap.trace_pow_eq_sum_pow_roots {K V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (f : Module.End K V) (k : ℕ) :
    LinearMap.trace K V (f ^ k) = (f.charpoly.roots.map (· ^ k)).sum := by
  classical

  let N := f.maxGenEigenspace
  have h_decomp : ⨆ μ, N μ = ⊤ := Module.End.iSup_maxGenEigenspace_eq_top f

  have h_indep : iSupIndep N := Module.End.independent_genEigenspace f ⊤

  have h_maps : ∀ μ, Set.MapsTo (f ^ k) (N μ) (N μ) := fun μ ↦
    Module.End.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right k) μ

  have h_finite : {μ | N μ ≠ ⊥}.Finite :=
    Submodule.finite_ne_bot_of_iSupIndep h_indep

  have : ∀ μ, Module.Finite K (N μ) := fun μ ↦ Module.IsNoetherian.finite K (N μ)
  have : ∀ μ, Module.Free K (N μ) := fun _ ↦ inferInstance

  have h_internal : DirectSum.IsInternal N :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top h_indep h_decomp

  rw [trace_eq_sum_trace_restrict' h_internal h_finite h_maps]

  have h_nil_restrict : ∀ μ, IsNilpotent ((f - algebraMap K (Module.End K V) μ).restrict
      (Module.End.mapsTo_maxGenEigenspace_of_comm
        (Algebra.mul_sub_algebraMap_commutes f μ) μ)) :=
    fun μ ↦ Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap f μ

  have h_trace_eigenspace : ∀ μ, trace K (N μ) ((f ^ k).restrict (h_maps μ)) =
      Module.finrank K (N μ) • (μ ^ k) := fun μ ↦ by

    rw [← Module.End.pow_restrict]
    exact trace_pow_eq_pow_smul_finrank_of_isNilpotent_sub_aux (f.restrict <|
      Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ) μ k (h_nil_restrict μ)
  simp_rw [h_trace_eigenspace]

  have h_finrank_eq : ∀ μ, Module.finrank K (N μ) = f.charpoly.rootMultiplicity μ :=
    fun μ ↦ finrank_maxGenEigenspace_eq f μ
  simp_rw [h_finrank_eq]

  rw [Finset.sum_multiset_map_count]

  have h_eigenvalue_iff_root : ∀ μ, N μ ≠ ⊥ ↔ μ ∈ f.charpoly.roots := fun μ ↦ by

    constructor
    · intro hne_bot

      rw [Polynomial.mem_roots f.charpoly_monic.ne_zero]

      have h_ev : f.HasEigenvalue μ := by
        by_contra h_not_ev
        rw [Module.End.hasEigenvalue_iff] at h_not_ev

        have : f.maxGenEigenspace μ = ⊥ := by

          rw [Module.End.maxGenEigenspace]
          simp only [Module.End.genEigenspace_top]

          by_contra h_max_ne

          have h_finrank_pos : 0 < Module.finrank K (f.maxGenEigenspace μ) := by
            rw [Module.finrank_pos_iff, Submodule.nontrivial_iff_ne_bot]

            rw [Module.End.maxGenEigenspace, Module.End.genEigenspace_top]
            exact h_max_ne
          rw [finrank_maxGenEigenspace_eq] at h_finrank_pos
          have h_is_root := Polynomial.rootMultiplicity_pos f.charpoly_monic.ne_zero |>.mp h_finrank_pos

          have h_in_roots : μ ∈ f.charpoly.roots :=
            Polynomial.mem_roots f.charpoly_monic.ne_zero |>.mpr h_is_root
          rw [charpoly_roots_eq_minpoly f μ] at h_in_roots
          have h_ev' := Module.End.hasEigenvalue_of_isRoot (Polynomial.mem_roots'.mp h_in_roots).2
          exact h_not_ev (Module.End.hasEigenvalue_iff.mp h_ev')
        exact hne_bot this
      have hroot_min := Module.End.isRoot_of_hasEigenvalue h_ev
      exact Polynomial.IsRoot.dvd hroot_min (minpoly_dvd_charpoly f)
    · intro hroot

      have h_mult_pos := Polynomial.rootMultiplicity_pos f.charpoly_monic.ne_zero |>.mpr
        (Polynomial.mem_roots f.charpoly_monic.ne_zero |>.mp hroot)
      rw [← finrank_maxGenEigenspace_eq] at h_mult_pos
      exact Submodule.nontrivial_iff_ne_bot.mp (Module.finrank_pos_iff.mp h_mult_pos)

  have h_finsets_eq : h_finite.toFinset = f.charpoly.roots.toFinset := by
    ext μ
    simp only [Set.Finite.mem_toFinset, Multiset.mem_toFinset]
    exact h_eigenvalue_iff_root μ
  rw [h_finsets_eq]

  apply Finset.sum_congr rfl
  intro μ hμ
  simp only [nsmul_eq_mul]
  congr 1

  rw [Polynomial.count_roots f.charpoly]

open Polynomial in
lemma Module.End.isNilpotent_iff_roots_charpoly {K V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (u : Module.End K V) :
    IsNilpotent u ↔ ∀ x : u.Eigenvalues, x.1 = 0 := by
  rw [LinearMap.isNilpotent_iff_charpoly, ← LinearMap.charpoly_natDegree u,
    ← roots_zero_iff' u.charpoly_monic, show (∀ x ∈ (LinearMap.charpoly u).roots, x = 0)
    ↔ ∀ x ∈ (minpoly K u).roots, x = 0 by simp [LinearMap.charpoly_roots_eq_minpoly u]]
  simp only [mem_roots', ne_eq, minpoly.ne_zero <| IsIntegral.of_finite K u, not_false_eq_true,
    ← hasEigenvalue_iff_isRoot, zero_lt_one, hasUnifEigenvalue_iff_hasUnifEigenvalue_one, true_and]
  exact ⟨fun hx x ↦ hx x.1 x.2, fun hx x hx' ↦ hx ⟨_, hx'⟩⟩

lemma Multiset.esymm_eq_zero_of_sum_pow_eq_zero {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (s : Multiset R) (h : ∀ k : ℕ, 1 ≤ k → k ≤ s.card → (s.map (· ^ k)).sum = 0) :
    ∀ k : ℕ, 1 ≤ k → k ≤ s.card → s.esymm k = 0 := by

  intro k hk1 hkn
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · omega
    · rcases k with _ | k
      ·

        show s.esymm 1 = 0
        rw [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map]
        simp only [Function.comp_apply, Multiset.prod_singleton, Multiset.map_id']
        convert h 1 (by omega) hkn using 2
        simp only [pow_one]
        exact (Multiset.map_id s).symm
      ·
        let n := k + 1 + 1

        have ⟨l, hl⟩ := s.exists_rep
        have hl_len : l.length = s.card := by rw [← hl]; simp
        let f : Fin s.card → R := fun i ↦ l.get (i.cast hl_len.symm)

        let t : Multiset R := (Finset.univ : Finset (Fin s.card)).val.map f

        have h_t_eq_s : t = s := by
          rw [← hl]

          simp only [t, Finset.val_univ_fin, Multiset.map_coe]
          congr 1
          simp only [List.finRange, List.map_ofFn]
          conv_rhs => rw [← List.ofFn_get l]
          apply List.ext_get
          · simp [hl_len]
          · intro i h1 h2
            bound

        have h_aeval_esymm : ∀ m : ℕ, (MvPolynomial.aeval f) (MvPolynomial.esymm (Fin s.card) R m) =
            s.esymm m := fun m ↦ by
          rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
          simp only [t] at h_t_eq_s
          rw [h_t_eq_s]

        have h_aeval_psum : ∀ m : ℕ, (MvPolynomial.aeval f) (MvPolynomial.psum (Fin s.card) R m) =
            (s.map (· ^ m)).sum := fun m ↦ by
          simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X]

          have : (∑ i : Fin s.card, f i ^ m) = (t.map (· ^ m)).sum := by
            simp only [t, Multiset.map_map, Function.comp_apply, Finset.val_univ_fin]
            simp only [Multiset.map_coe, Multiset.sum_coe]
            rfl
          rw [this, h_t_eq_s]

        have newton := MvPolynomial.mul_esymm_eq_sum (Fin s.card) R n

        apply_fun (MvPolynomial.aeval f) at newton
        rw [map_mul, map_natCast, h_aeval_esymm] at newton
        rw [map_mul, map_pow, map_neg, map_one, map_sum] at newton
        simp only [map_mul, map_pow, map_neg, map_one, h_aeval_esymm, h_aeval_psum] at newton

        have sum_eq_zero : ∑ x ∈ Finset.filter (fun x ↦ x.1 < n) (Finset.antidiagonal n),
            (-1) ^ x.1 * s.esymm x.1 * (s.map (· ^ x.2)).sum = 0 := by
          apply Finset.sum_eq_zero
          intro ⟨i, j⟩ hij
          simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hij
          obtain ⟨h_ij_sum, hi_lt_n⟩ := hij

          by_cases hi : i = 0
          ·
            subst hi
            simp only [zero_add] at h_ij_sum
            subst h_ij_sum
            have hj_ge_1 : 1 ≤ n := by omega
            have hj_le_card : n ≤ s.card := hkn
            simp only [h n hj_ge_1 hj_le_card, mul_zero]
          ·
            have hi_ge_1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi
            have hi_lt_k2 : i < n := hi_lt_n
            have hi_le_card : i ≤ s.card := le_trans (le_of_lt hi_lt_k2) hkn
            have h_esymm_i_zero := ih i hi_lt_k2 hi_ge_1 hi_le_card
            simp only [h_esymm_i_zero, mul_zero, zero_mul]
        rw [sum_eq_zero, mul_zero] at newton

        have h_nsmul : n • s.esymm n = 0 := by simp only [nsmul_eq_mul]; exact newton
        cases NoZeroSMulDivisors.eq_zero_or_eq_zero_of_smul_eq_zero h_nsmul with
        | inl h_n => exact absurd h_n (by omega : n ≠ 0)
        | inr h_esymm => exact h_esymm

open Polynomial in

lemma Multiset.all_eq_zero_of_esymm_eq_zero {R : Type*} [CommRing R] [IsDomain R]
    (s : Multiset R) (h : ∀ k : ℕ, 1 ≤ k → k ≤ s.card → s.esymm k = 0) :
    ∀ x ∈ s, x = 0 := by
  intro x hx

  let P := (s.map fun r => X - C r).prod

  have hx_root : P.IsRoot x := by
    simp only [P, IsRoot, Polynomial.eval_multiset_prod, Multiset.map_map]
    apply Multiset.prod_eq_zero
    simp only [Multiset.mem_map, Function.comp_apply, eval_sub, eval_X, eval_C]
    exact ⟨x, hx, sub_self x⟩

  have hP_eq : P = X ^ s.card := by
    show (s.map fun t => X - C t).prod = X ^ s.card
    rw [Multiset.prod_X_sub_X_eq_sum_esymm]

    rw [Finset.sum_eq_single 0]
    ·
      simp only [pow_zero, one_mul, Nat.sub_zero, Multiset.esymm, Multiset.powersetCard_zero_left,
        Multiset.map_singleton, Multiset.prod_zero, Multiset.sum_singleton, map_one, one_mul]
    ·
      intro j hj hj0
      simp only [Finset.mem_range] at hj
      have hj' : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
      have hj'' : j ≤ s.card := by omega
      simp only [h j hj' hj'', C_0, zero_mul, mul_zero]
    ·
      intro h0
      simp at h0

  rw [hP_eq] at hx_root
  simp only [IsRoot, eval_pow, eval_X] at hx_root
  exact eq_zero_of_pow_eq_zero hx_root

lemma Module.End.isNilpotent_of_pow_trace_eq_zero (K V : Type*) [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (u : Module.End K V) :
    (∀ n : ℕ, 1 ≤ n → LinearMap.trace K _ (u ^ n) = 0)
    ↔ IsNilpotent u := by
  fconstructor
  · intro h

    let K' := AlgebraicClosure K
    have : IsAlgClosed K' := AlgebraicClosure.isAlgClosed K
    have : CharZero K' := charZero_of_injective_algebraMap
      (algebraMap K K').injective

    rw [LinearMap.isNilpotent_iff_charpoly]

    have hdeg : (u.charpoly.map (algebraMap K K')).natDegree = u.charpoly.natDegree := by
      exact Polynomial.natDegree_map_eq_of_injective (algebraMap K K').injective _
    have hp : u.charpoly.map (algebraMap K K') =
        Polynomial.X ^ (u.charpoly.map (algebraMap K K')).natDegree := by
      rw [← Polynomial.roots_zero_iff' (u.charpoly_monic.map (algebraMap K K'))]
      intro x hx
      rw [Polynomial.mem_roots_map u.charpoly_monic.ne_zero] at hx

      let u' := u.baseChange K'
      let V' := TensorProduct K K' V
      have : FiniteDimensional K' V' := Module.Finite.base_change K K' V
      have h_charpoly : u'.charpoly = u.charpoly.map (algebraMap K K') :=
        LinearMap.charpoly_baseChange u K'

      let S := u'.charpoly.roots
      have h_splits : u'.charpoly.Splits := IsAlgClosed.splits _
      have h_card : S.card = u'.charpoly.natDegree := Polynomial.splits_iff_card_roots.mp h_splits

      have h_trace_K' : ∀ k : ℕ, 1 ≤ k → LinearMap.trace K' V' (u' ^ k) = 0 := fun k hk => by
        rw [← LinearMap.baseChange_pow, LinearMap.trace_baseChange, h k hk, RingHom.map_zero]

      have h_power_sums : ∀ k : ℕ, 1 ≤ k → k ≤ S.card → (S.map (· ^ k)).sum = 0 := by
        intro k hk hkn

        rw [← LinearMap.trace_pow_eq_sum_pow_roots u' k]
        exact h_trace_K' k hk

      have h_esymm_zero : ∀ k : ℕ, 1 ≤ k → k ≤ S.card → S.esymm k = 0 :=
        Multiset.esymm_eq_zero_of_sum_pow_eq_zero S h_power_sums

      have h_all_zero : ∀ y ∈ S, y = 0 := Multiset.all_eq_zero_of_esymm_eq_zero S h_esymm_zero

      have hx_in_S : x ∈ S := by
        show x ∈ u'.charpoly.roots
        rw [h_charpoly]
        exact Polynomial.mem_roots_map u.charpoly_monic.ne_zero |>.mpr hx
      exact h_all_zero x hx_in_S

    have hinj := Polynomial.map_injective (algebraMap K K') (algebraMap K K').injective
    rw [hdeg, LinearMap.charpoly_natDegree] at hp
    apply hinj
    rw [hp, Polynomial.map_pow, Polynomial.map_X]
  · intro hu n hn
    by_cases h : finrank K V = 0
    · rw [finrank_zero_iff_forall_zero] at h
      suffices u = 0 by simp [this, zero_pow (show n ≠ 0 by omega)]
      ext x
      simp [h (u x)]
    · let b := Module.finBasis K V
      rw [LinearMap.trace_eq_matrix_trace K b (u ^ n)]
      have hnon : Nonempty (Fin (finrank K V)) := Fin.pos_iff_nonempty.mp (Nat.zero_lt_of_ne_zero h)
      simp [Matrix.trace_eq_neg_charpoly_coeff]
      suffices LinearMap.charpoly (u ^ n) = Polynomial.X ^ finrank K V by simp [this]; omega
      rwa [← LinearMap.isNilpotent_iff_charpoly, IsNilpotent.pow_iff_pos (by omega)]
