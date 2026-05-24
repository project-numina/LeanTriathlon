/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

lemma ContinuousLinearMap.hasEigenvalue_le_opNorm {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (T : E →L[𝕜] E) {a : 𝕜} (h : Module.End.HasEigenvalue T.toLinearMap a) :
    ‖a‖ ≤ ‖T‖ := by
  obtain ⟨v, hv_mem, hv_ne⟩ := h.exists_hasEigenvector
  refine le_of_mul_le_mul_right ?_ (norm_pos_iff.mpr hv_ne)
  rw [← norm_smul, ← Module.End.mem_eigenspace_iff.mp hv_mem]
  exact T.le_opNorm v
