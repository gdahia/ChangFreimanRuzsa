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
# The coordinate map of a generalized arithmetic progression

A generalized arithmetic progression of dimension $d$ in an additive monoid $G$ with origin $a$,
steps $s_1, \dots, s_d$ and lengths $L_1, \dots, L_d$ is the set of the points
$a + w_1 s_1 + \dots + w_d s_d$ with $0 \le w_i < L_i$. This file defines the map `gapMap` that
sends a vector of coordinates $w$ to that point.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open Nat
open scoped Pointwise

noncomputable section

/-- The point $a + \sum_i w_i s_i$ of the generalized arithmetic progression with origin $a$,
steps $s_i$ and lengths $L_i$, for coordinates $0 \le w_i < L_i$. -/
def gapMap {G : Type*} [AddCommMonoid G] {d : ℕ} (origin : G) (step : Fin d → G)
    (length : Fin d → ℕ) (w : (i : Fin d) → Fin (length i)) : G := origin + ∑ i, (w i : ℕ) • step i

end

end ChangFreimanRuzsa
