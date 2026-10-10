/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Order.Int.ConditionallyCompleteOrder
import Mathlib.Data.Set.Card

/-!
GAPs
-/

@[expose] public section

namespace ChangFreimanRuzsa

open Nat
open scoped Pointwise

noncomputable section

def gapMap {G : Type*} [AddCommMonoid G] {d : ℕ} (origin : G) (step : Fin d → G)
    (length : Fin d → ℕ) (w : (i : Fin d) → Fin (length i)) : G := origin + ∑ i, (w i : ℕ) • step i

end

end ChangFreimanRuzsa
