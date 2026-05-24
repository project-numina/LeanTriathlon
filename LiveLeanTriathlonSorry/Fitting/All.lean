/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.GroupTheory.Nilpotent
public import LiveLeanTriathlonSorry.Util.Attributes
@[expose] public section

section Background

open scoped commutatorElement

variable {G : Type*} [Group G]

def commFin (H : ℕ → Subgroup G) (n : ℕ) : Subgroup G :=
  match n with
  | 0 => H 0
  | n + 1 => ⁅commFin H n, H (n + 1)⁆

end Background

section Main

open scoped commutatorElement

private instance iSup_normal {G : Type*} [Group G] {ι : Type*} (H : ι → Subgroup G)
    [hN : ∀ i, (H i).Normal] : (⨆ i, H i).Normal := by
  constructor
  intro n hn g
  refine Subgroup.iSup_induction H (C := fun x => ∀ g : G, g * x * g⁻¹ ∈ ⨆ i, H i) hn ?_ ?_ ?_ g
  .
    intro i x hx g
    exact Subgroup.mem_iSup_of_mem i ((hN i).conj_mem x hx g)
  .
    intro g; simp
  .
    intro x y hx hy g
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]; exact (⨆ i, H i).mul_mem (hx g) (hy g)

private abbrev BoolToSub {G : Type*} [Group G] (M N : Subgroup G) (b : Bool) : Subgroup G :=
  if b then M else N

private abbrev CF {G : Type*} [Group G] (M N : Subgroup G) (σ : ℕ → Bool) (k : ℕ) : Subgroup G :=
  commFin (fun i => BoolToSub M N (σ i)) k

set_option maxHeartbeats 800000 in

@[AMS 20]
theorem fitting {G : Type*} [Group G] (M N : Subgroup G) (hM₁ : M.Normal) (hN₁ : N.Normal)
    (m n : ℕ)
    (hM₂ : Group.IsNilpotent M) (hM₃ : Group.nilpotencyClass M = m)
    (hN₂ : Group.IsNilpotent N) (hN₃ : Group.nilpotencyClass N = n) :
    ∃ _ : Group.IsNilpotent ↥(M ⊔ N), Group.nilpotencyClass ↥(M ⊔ N) ≤ m + n := by sorry

end Main
