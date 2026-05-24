/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import LiveLeanTriathlonSorry.Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import LiveLeanTriathlonSorry.Util.Attributes

@[expose] public section

open CategoryTheory Limits Functor

universe u v

variable {I : Type u} [Preorder I] (F : Iᵒᵖ ⥤ Type v) [hI : Countable I] [IsDirected I (· ≤ ·)]

set_option backward.isDefEq.respectTransparency false in
open ShortComplex Opposite in
@[stacks 0598, AMS 18]
theorem IsMittagLeffler.mapShortExact (S : ShortComplex (Iᵒᵖ ⥤ Ab)) (hS : S.ShortExact)
    (hA : (S.X₁ ⋙ forget Ab).IsMittagLeffler) : (S.map lim).ShortExact := by sorry
