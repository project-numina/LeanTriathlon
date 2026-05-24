/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/
module

public import Mathlib.Order.Interval.Finset.Defs

@[expose] public section

lemma Finset.Iio_union_Ioi {ι} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
    [LocallyFiniteOrderTop ι] [DecidableEq ι] (i : ι) :
    (Finset.Iio i) ∪ (Finset.Ioi i) = Finset.univ \ {i} := by grind
