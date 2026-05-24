/-
Copyright (c) 2025 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Init.Classical

@[expose] public section

universe u

theorem choose_ne_choose {α : Sort u} {p : α → Prop} {q : α → Prop}
    (hp : ∃ x, p x) (hq : ∃ y, q y) (hn : ∀ x y, p x → q y → x ≠ y) :
    Classical.choose hp ≠ Classical.choose hq :=
fun h_eq ↦ hn _ _ (Classical.choose_spec hp) (Classical.choose_spec hq) h_eq
