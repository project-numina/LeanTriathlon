/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey and Numina team
-/
module

public import Mathlib.CategoryTheory.CofilteredSystem

@[expose] public section

open CategoryTheory Limits Functor

lemma eventualRange_eq_univ_of_surjective.{u, v} {I : Type u} [Preorder I] (F : Iᵒᵖ ⥤ Type v)
    (hF : ∀ (i j : Iᵒᵖ) (f : i ⟶ j),
    Function.Surjective (F.map f)) (j : Iᵒᵖ) : F.eventualRange j = Set.univ :=
  Set.ext fun x ↦ by simpa [mem_eventualRange_iff] using fun _ _ ↦ hF ..

lemma sections_nonempty_of_surjective_countable.{u, v} {I : Type u} [Preorder I] (F : Iᵒᵖ ⥤ Type v)
    [hI : Countable I] [hne : Nonempty I]
    (hdir : IsDirected I (· ≤ ·)) (hobj : ∀ j : Iᵒᵖ, Nonempty (F.obj j))
    (hsur : ∀ (i j : Iᵒᵖ) (f : i ⟶ j), Function.Surjective (F.map f)) :
    F.sections.Nonempty := by
  obtain ⟨enum, henum⟩ := countable_iff_exists_surjective.mp hI
  let m : ℕ → I := Nat.rec (enum 0) fun n ih => (hdir.directed ih (enum (n + 1))).choose
  have hm_spec1 n := (hdir.directed (m n) (enum (n + 1))).choose_spec.1
  have hm_spec2 n := (hdir.directed (m n) (enum (n + 1))).choose_spec.2
  have hm_enum n : enum n ≤ m n := n.rec le_rfl <| fun n _ ↦ hm_spec2 n
  have hm_cofinal i : ∃ n, i ≤ m n := ⟨henum i|>.choose, by
    convert hm_enum (henum i).choose; exact henum i|>.choose_spec.symm⟩
  let step n := (homOfLE (hm_spec1 n)).op
  let x : (n : ℕ) → F.obj (Opposite.op (m n)) :=
    Nat.rec (hobj _).some fun n ih => (hsur _ _ (step n) ih).choose
  have hx n : F.map (step n) (x (n + 1)) = x n := (hsur _ _ (step n) _).choose_spec
  have hm_mono' a b (hab : a ≤ b) : m a ≤ m b := Nat.le.rec le_rfl (by grind) hab
  have hx' n1 n2 (h : n1 ≤ n2) : F.map (homOfLE (hm_mono' n1 n2 h)).op (x n2) = x n1 := by
    induction h with | refl => simp | @step k hk ih =>
    rw [← homOfLE_comp (hm_mono' n1 k hk) (hm_spec1 k), CategoryTheory.op_comp,
      F.map_comp, types_comp_apply, hx, ih]
  let s j : F.obj j := F.map (homOfLE (hm_cofinal j.unop).choose_spec).op (x (hm_cofinal j.unop).choose)
  refine ⟨s, fun {i j} f => ?_⟩
  obtain ⟨n, hn_i, hn_j⟩ := @IsDirected.directed _ (· ≤ ·) SemilatticeSup.instIsDirectedOrder
    (hm_cofinal i.unop).choose (hm_cofinal j.unop).choose
  simp only [Opposite.op_unop, homOfLE_leOfHom, s, ← hx' _ n hn_i, ← hx' _ n hn_j,
    ← CategoryTheory.Functor.map_comp_apply]
  congr 1
