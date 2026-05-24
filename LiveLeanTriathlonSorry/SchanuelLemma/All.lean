/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module
public import Mathlib.Algebra.AddTorsor.Defs
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.Projective
public import LiveLeanTriathlonSorry.Util.Attributes
@[expose] public section

section Main

open LinearMap CategoryTheory

universe w u v

variable {R : Type u} [Ring R] {K P1 L P2 N M : ModuleCat.{v} R} {c1 : K ⟶ P1} {p1 : P1 ⟶ M}
  {c2 : L ⟶ P2} {p2 : P2 ⟶ M} (h1 : c1 ≫ p1 = 0) (h2 : c2 ≫ p2 = 0)
  (hS1 : (ShortComplex.mk c1 p1 h1).ShortExact) (hS2 : (ShortComplex.mk c2 p2 h2).ShortExact)
  [Module.Projective R P1] [Module.Projective R P2]

variable (P1 P2)

abbrev S1' : ShortComplex (ModuleCat R) where
  X₁ := ModuleCat.of R (K × P2)
  X₂ := ModuleCat.of R (P1 × P2)
  X₃ := ModuleCat.of R M
  f := ModuleCat.ofHom (c1.hom.prodMap .id)
  g := ModuleCat.ofHom (LinearMap.fst R _ _) ≫ p1
  zero := by
    ext k
    .
      simp only [ModuleCat.of_coe, ModuleCat.hom_comp, ModuleCat.hom_ofHom, coe_comp, coe_fst,
        coe_inl, Function.comp_apply, prodMap_apply, id_coe, id_eq, ModuleCat.hom_zero, zero_comp]
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, h1, ModuleCat.hom_zero]
    .
      simp

abbrev S2' : ShortComplex (ModuleCat R) where
  X₁ := ModuleCat.of R (P1 × L)
  X₂ := ModuleCat.of R (P1 × P2)
  X₃ := ModuleCat.of R M
  f := ModuleCat.ofHom (LinearMap.id.prodMap c2.hom)
  g := ModuleCat.ofHom (LinearMap.snd R _ _) ≫ p2
  zero := by
    ext l
    .
      simp
    .
      simp only [ModuleCat.of_coe, ModuleCat.hom_comp, ModuleCat.hom_ofHom, coe_comp, coe_snd,
        coe_inr, Function.comp_apply, prodMap_apply, id_coe, id_eq, ModuleCat.hom_zero, zero_comp]
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, h2, ModuleCat.hom_zero]

variable {P1 P2} (p1 p2) in

abbrev S3 : ShortComplex (ModuleCat R) where
  X₁ := ModuleCat.of R (LinearMap.coprod p1.hom p2.hom).ker
  X₂ := ModuleCat.of R (P1 × P2)
  X₃ := ModuleCat.of R M
  f := ModuleCat.ofHom (LinearMap.coprod p1.hom p2.hom).ker.subtype
  g := ModuleCat.ofHom <| LinearMap.coprod p1.hom p2.hom

section prerequisites
omit [Module.Projective R ↑P1] [Module.Projective R ↑P2]

variable {P1 P2 h1 h2}

end prerequisites

@[stacks 00O3 "(ii)"]
noncomputable def Schanuel1 (hS1 : (S1' P1 P2 h1).ShortExact) (hS2 : (S2' P1 P2 h2).ShortExact) :
    S1' P1 P2 h1 ≅ S3 (p1 := p1) (p2 := p2) := by sorry

end Main
