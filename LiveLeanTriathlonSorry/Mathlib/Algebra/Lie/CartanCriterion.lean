/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Lie.Killing
public import LiveLeanTriathlonSorry.Mathlib.Algebra.Lie.HumphreysLemmaGeneral
public import Mathlib.Algebra.Lie.Engel

@[expose] public section

@[expose] public section

open LieAlgebra LieModule LinearMap Module

namespace LieAlgebra

variable (K L : Type*) [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [Module.Finite K L]

instance IsSemisimple.instIsKilling [IsSemisimple K L] : IsKilling K L where
  killingCompl_top_eq_bot := by

    set S := LieIdeal.killingCompl K L ⊤
    set SS : LieIdeal K L := ⁅S, S⁆

    let ad_lin : L →ₗ[K] End K L := (ad K L : L →ₗ⁅K⁆ End K L)
    set A : Submodule K (End K L) :=
      (SS : LieSubmodule K L L).toSubmodule.map ad_lin
    set B : Submodule K (End K L) :=
      (S : LieSubmodule K L L).toSubmodule.map ad_lin
    have hAB : A ≤ B := Submodule.map_mono
      ((LieSubmodule.toSubmodule_le_toSubmodule SS S).mpr (LieSubmodule.lie_le_left S S))

    have ad_nil : ∀ x ∈ (SS : LieSubmodule K L L).toSubmodule,
        IsNilpotent (ad_lin x) := by
      intro x hx
      apply humphreys_lemma A B hAB

      · intro b hb
        obtain ⟨s, hs, rfl⟩ := hb

        change ⁅ad_lin x, ad_lin s⁆ ∈ A
        have h_lie : ad_lin ⁅x, s⁆ = ⁅ad_lin x, ad_lin s⁆ := LieHom.map_lie (ad K L) x s
        rw [← h_lie]
        apply Submodule.mem_map_of_mem

        have hx_SS : x ∈ (SS : LieSubmodule K L L) := hx
        have hs_S : s ∈ (S : LieSubmodule K L L) := hs

        exact LieSubmodule.lie_le_left SS S (LieSubmodule.lie_mem_lie hx_SS hs_S)

      · intro z hz

        have hx' : x ∈ Submodule.span K {⁅a, b⁆ | (a ∈ (S : LieSubmodule K L L))
            (b ∈ (S : LieSubmodule K L L))} := by
          rw [← LieSubmodule.lieIdeal_oper_eq_linear_span']; exact hx

        refine Submodule.span_induction (p := fun x _ =>
            trace K L (ad_lin x * z) = 0) ?_ ?_ ?_ ?_ hx'

        · rintro _ ⟨a, ha, b, hb, rfl⟩

          have h_lie : ad_lin ⁅a, b⁆ = ad_lin a * ad_lin b - ad_lin b * ad_lin a := by
            have := LieHom.map_lie (ad K L) a b
            rw [Ring.lie_def] at this
            exact this
          rw [h_lie, sub_mul, map_sub,
            ← trace_mul_cycle (R := K) (M := L) (ad_lin a) z (ad_lin b), ← map_sub,
            show ad_lin a * ad_lin b * z - ad_lin a * z * ad_lin b =
              ad_lin a * (ad_lin b * z - z * ad_lin b)
              by simp only [mul_sub, mul_assoc]]

          have hb_in_B : ad_lin b ∈ B := Submodule.mem_map_of_mem hb
          have hz_comm : ad_lin b * z - z * ad_lin b ∈ A := by
            have h := hz (ad_lin b) hb_in_B
            rw [show ⁅z, ad_lin b⁆
              = z * ad_lin b - ad_lin b * z from Ring.lie_def z (ad_lin b)] at h
            have := A.neg_mem h
            rwa [neg_sub] at this

          obtain ⟨w, hw, hwz⟩ := hz_comm
          rw [← hwz]

          change (trace K L) ((ad K L) a ∘ₗ (ad K L) w) = 0
          rw [← killingForm_apply_apply, LieModule.traceForm_comm]
          exact (LieIdeal.mem_killingCompl K L ⊤).mp ha w (LieSubmodule.mem_top w)

        · simp

        · intro x₁ x₂ _ _ h1 h2
          rw [map_add, add_mul, map_add, h1, h2, add_zero]

        · intro c x₁ _ h1
          rw [map_smul, smul_mul_assoc, LinearMap.map_smul, h1, smul_zero]

    have ss_nilpotent : LieRing.IsNilpotent ↥SS := by
      have : IsNoetherian K ↥SS := LieSubmodule.instIsNoetherianSubtypeMem SS
      rw [LieAlgebra.isNilpotent_iff_forall (R := K)]
      intro ⟨x, hx⟩
      obtain ⟨n, hn⟩ := ad_nil x hx

      have h_inv : ∀ y ∈ (SS : LieSubmodule K L L).toSubmodule,
          ad_lin x y ∈ (SS : LieSubmodule K L L).toSubmodule :=
        fun _ hy => SS.lie_mem hy

      have h_eq : ad K ↥SS ⟨x, hx⟩ = (ad_lin x).restrict h_inv := by
        ext ⟨_, _⟩; rfl
      refine ⟨n, ?_⟩
      rw [h_eq]
      have e := End.pow_apply_mem_of_forall_mem n h_inv
      have f : Eq (α := End K ↥SS) (restrict (ad_lin x) h_inv ^ n : End K ↥SS) ((ad_lin x ^ n).restrict e : End K ↥SS) := by
        exact End.pow_restrict n h_inv e
      rw [f]
      ext ⟨y, hy⟩

      simp only [LinearMap.restrict_apply, zero_apply]

      exact LinearMap.congr_fun hn y

    have ss_solvable : IsSolvable ↥SS := inferInstance
    have s_solvable : IsSolvable ↥S := by
      obtain ⟨k, hk⟩ := (isSolvable_iff K ↥SS).mp ss_solvable
      rw [LieIdeal.derivedSeries_eq_bot_iff] at hk
      apply IsSolvable.mk (R := K) (k := k + 1)
      rw [LieIdeal.derivedSeries_eq_bot_iff, derivedSeriesOfIdeal_add,
        derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero]
      exact hk

    exact HasTrivialRadical.eq_bot_of_isSolvable S

end LieAlgebra
