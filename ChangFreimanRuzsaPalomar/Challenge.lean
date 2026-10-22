/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib

/-!
# Chang's theorem

Chang's polynomial form of Freiman's theorem for finite sets of integers and for subsets of
`ZMod q` with `q` prime: a set with small doubling lies in a `2`-proper generalized arithmetic
progression of comparable size.

A generalized arithmetic progression has an `origin` and a finitely supported `bound`, and its
points are `origin + ∑ v, c v • v` with `c ≤ bound`. It is `2`-proper when `P + P` is proper, a
weaker condition than the `2`-properness of Green and Tao.

The proofs are in `Solution.lean`.
-/

@[expose] public section

open Finset
open scoped Pointwise

namespace ChangFreimanRuzsa

noncomputable section

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

/-- **Chang's theorem** for sets of integers. A finite nonempty set `X` of integers with
`#(X + X) ≤ κ * #X`, where `2 ≤ κ`, is contained in a `2`-proper generalized arithmetic
progression of dimension at most `2 * κ - 1` with at most `Real.exp (10 ^ 32 * κ ^ 7) * #X`
points. -/
theorem exists_twoProperGAP_subset_dim_le_card_le' {κ : ℝ} (X : Finset ℤ) (hX : X.Nonempty)
    (hκ : 2 ≤ κ) (hXX : (#(X + X) : ℝ) ≤ κ * #X) :
    ∃ P : GAP ℤ, P.TwoProper ∧ X ⊆ P.carrier ∧ (P.dim : ℝ) ≤ 2 * κ - 1 ∧
      (#P.carrier : ℝ) ≤ Real.exp (10 ^ 32 * κ ^ 7) * #X :=
  sorry

/-- **Chang's theorem** in `ZMod q` for a prime `q`. A set `X` with `#(X + X) ≤ κ * #X`, where
`2 ≤ κ`, with at least `7 * 10 ^ 7 * κ ^ 2` elements and with
`Real.exp (10 ^ 30 * κ ^ 7) * #X ≤ q`, is contained in a `2`-proper generalized arithmetic
progression of dimension at most `2 * κ - 1` with at most `Real.exp (10 ^ 30 * κ ^ 7) * #X`
points. -/
theorem exists_twoProperGAP_zmod_subset_dim_le_card_le' {q : ℕ} {κ : ℝ} (X : Finset (ZMod q))
    (hq : q.Prime) (hκ : 2 ≤ κ) (hXX : (#(X + X) : ℝ) ≤ κ * #X)
    (hXlower : 7 * 10 ^ 7 * κ ^ 2 ≤ #X)
    (hXupper : Real.exp (10 ^ 30 * κ ^ 7) * #X ≤ q) :
    ∃ Q : GAP (ZMod q), Q.TwoProper ∧ X ⊆ Q.carrier ∧ (Q.dim : ℝ) ≤ 2 * κ - 1 ∧
      (#Q.carrier : ℝ) ≤ Real.exp (10 ^ 30 * κ ^ 7) * #X :=
  sorry

end ChangFreimanRuzsa
