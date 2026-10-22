/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Data.Finsupp.Interval
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Generalized arithmetic progressions

A generalized arithmetic progression in an additive monoid $G$ is given by an origin $x_0 \in G$
and a finitely supported bound $b : G \to \mathbb{N}$. Its points are $x_0 + \sum_v c_v v$ with
$c \le b$. The steps are the elements $v$ with $b_v \ne 0$, and the length of the step $v$ is
$b_v + 1$. The sum of two progressions adds the origins and the bounds, so that the points of
$P + Q$ are the sums of a point of $P$ and a point of $Q$.

A progression $P$ is $2$-proper when $P + P$ is proper, as in Bilu's condition $F_2$ and in Tao and
Vu. Green and Tao call a progression with numbered steps $s_i$ and lengths $\ell_i$ $2$-proper when
the points $2 x_0 + \sum_i w_i s_i$ with $0 \le w_i < 2 \ell_i$ are distinct. The points of $P + P$
are those with $0 \le w_i \le 2 \ell_i - 2$, so the condition of Green and Tao is stronger. The
progression $\{0, 1\}$ in $\mathbb{Z}/3\mathbb{Z}$ is $2$-proper but not $2$-proper in the sense of
Green and Tao.

## Main definitions

* `GAP G`: a generalized arithmetic progression in `G`, not necessarily proper.
* `GAP.carrier`, `GAP.dim`: its set of points and its number of steps.
* `GAP.Proper`: the points $x_0 + \sum_v c_v v$ with $c \le b$ are distinct.
* `GAP.TwoProper`: the progression $P + P$ is proper.
* `gapMap`: the point $x_0 + \sum_i w_i s_i$ of the progression with numbered steps $s_i$ and
  lengths $\ell_i$, for coordinates $0 \le w_i < \ell_i$.
-/

@[expose] public section

namespace ChangFreimanRuzsa

noncomputable section

/-- The point $a + \sum_i w_i s_i$ of the generalized arithmetic progression with origin $a$,
steps $s_i$ and lengths $L_i$, for coordinates $0 \le w_i < L_i$. -/
def gapMap {G : Type*} [AddCommMonoid G] {d : ℕ} (origin : G) (step : Fin d → G)
    (length : Fin d → ℕ) (w : (i : Fin d) → Fin (length i)) : G := origin + ∑ i, (w i : ℕ) • step i

/-- A generalized arithmetic progression, not necessarily proper: the set of the points
`origin + ∑ v, c v • v` with `c ≤ bound`. -/
structure GAP (G : Type*) [AddCommMonoid G] where
  /-- The base point. -/
  origin : G
  /-- The bound on the coefficient of each step. -/
  bound : G →₀ ℕ

namespace GAP

variable {G : Type*} [AddCommMonoid G]

/-- The point `origin + ∑ v, c v • v`. -/
def eval (P : GAP G) (c : G →₀ ℕ) : G := P.origin + c.sum fun v n ↦ n • v

/-- The set of points of a progression. -/
def carrier [DecidableEq G] (P : GAP G) : Finset G := (Finset.Iic P.bound).image P.eval

/-- The dimension of a progression: the number of its steps. -/
def dim (P : GAP G) : ℕ := P.bound.support.card

/-- A progression is proper if the points `origin + ∑ v, c v • v` with `c ≤ bound` are
distinct. -/
def Proper (P : GAP G) : Prop := Set.InjOn P.eval (Set.Iic P.bound)

/-- The sum of two progressions adds the origins and the bounds. -/
instance : Add (GAP G) where
  add P Q := ⟨P.origin + Q.origin, P.bound + Q.bound⟩

/-- A progression is `2`-proper if the progression `P + P` is proper. Green and Tao ask instead
that the points `2 • origin + ∑ i, w i • s i` with `w i < 2 * ℓ i` be distinct, for the steps
`s i` and the lengths `ℓ i`, which is a stronger condition. -/
def TwoProper (P : GAP G) : Prop := (P + P).Proper

end GAP

end

end ChangFreimanRuzsa
