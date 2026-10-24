/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Finsupp.Interval
public import Mathlib.Data.Nat.Prime.Defs

/-!
# Chang's theorem

Chang's polynomial form of Freiman's theorem for finite sets of integers and for subsets of
`ZMod q` with `q` prime: a set with small doubling lies in a `2`-proper generalized arithmetic
progression of comparable size. Also the Bogolyubov–Ruzsa lemma, the first step of its proof:
for such a set `X`, the set `X + X - (X + X)` contains a large proper generalized arithmetic
progression.

A generalized arithmetic progression has an `origin` and a finitely supported `bound`, and its
points are `origin + ∑ v, c v • v` with `c ≤ bound`. It is `2`-proper when `P + P` is proper.

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

end GAP

end

/-- **Bogolyubov–Ruzsa lemma** for sets of integers. If a finite set `X` of integers satisfies
`#(X + X) ≤ κ * #X`, where `2 ≤ κ`, and has at least `7 * 10 ^ 7 * κ ^ 2` elements, then
`X + X - (X + X)` contains a proper generalized arithmetic progression `Q` of dimension at most
`3 * 10 ^ 5 * κ ^ 2` with `#X ≤ Real.exp (2 * 10 ^ 7 * κ ^ 2) * #Q.carrier`. -/
theorem exists_proper_gap_subset_add_sub_add_dim_le_card_le' {κ : ℝ} (X : Finset ℤ) (hκ : 2 ≤ κ)
    (hXX : #(X + X) ≤ κ * #X) (hXlower : 7 * 10 ^ 7 * κ ^ 2 ≤ #X) :
    ∃ Q : GAP ℤ, Q.Proper ∧ Q.carrier ⊆ X + X - (X + X) ∧ Q.dim ≤ 3 * 10 ^ 5 * κ ^ 2 ∧
      #X ≤ Real.exp (2 * 10 ^ 7 * κ ^ 2) * #Q.carrier :=
  sorry

/-- **Bogolyubov–Ruzsa lemma** in `ZMod q` for a prime `q`. If a set `X` satisfies
`#(X + X) ≤ κ * #X`, where `2 ≤ κ`, and has at least `7 * 10 ^ 7 * κ ^ 2` elements, then
`X + X - (X + X)` contains a proper generalized arithmetic progression `Q` of dimension at most
`3 * 10 ^ 5 * κ ^ 2` with `#X ≤ Real.exp (2 * 10 ^ 7 * κ ^ 2) * #Q.carrier`. -/
theorem exists_proper_gap_zmod_subset_add_sub_add_dim_le_card_le' {q : ℕ} {κ : ℝ}
    (X : Finset (ZMod q)) (hq : q.Prime) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X)
    (hXlower : 7 * 10 ^ 7 * κ ^ 2 ≤ #X) :
    ∃ Q : GAP (ZMod q), Q.Proper ∧ Q.carrier ⊆ X + X - (X + X) ∧ Q.dim ≤ 3 * 10 ^ 5 * κ ^ 2 ∧
      #X ≤ Real.exp (2 * 10 ^ 7 * κ ^ 2) * #Q.carrier :=
  sorry

/-- **Chang's theorem** for sets of integers. A finite nonempty set `X` of integers with
`#(X + X) ≤ κ * #X`, where `2 ≤ κ`, is contained in a `2`-proper generalized arithmetic
progression of dimension at most `2 * κ - 1` with at most `Real.exp (10 ^ 32 * κ ^ 7) * #X`
points. -/
theorem exists_twoProperGAP_subset_dim_le_card_le' {κ : ℝ} (X : Finset ℤ) (hX : X.Nonempty)
    (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X) :
    ∃ P : GAP ℤ, (P + P).Proper ∧ X ⊆ P.carrier ∧ P.dim ≤ 2 * κ - 1 ∧
      #P.carrier ≤ Real.exp (10 ^ 32 * κ ^ 7) * #X :=
  sorry

/-- **Chang's theorem** in `ZMod q` for a prime `q`. A set `X` with `#(X + X) ≤ κ * #X`, where
`2 ≤ κ`, with at least `7 * 10 ^ 7 * κ ^ 2` elements and with
`Real.exp (10 ^ 30 * κ ^ 7) * #X ≤ q`, is contained in a `2`-proper generalized arithmetic
progression of dimension at most `2 * κ - 1` with at most `Real.exp (10 ^ 30 * κ ^ 7) * #X`
points. -/
theorem exists_twoProperGAP_zmod_subset_dim_le_card_le' {q : ℕ} {κ : ℝ} (X : Finset (ZMod q))
    (hq : q.Prime) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X) (hXlower : 7 * 10 ^ 7 * κ ^ 2 ≤ #X)
    (hXupper : Real.exp (10 ^ 30 * κ ^ 7) * #X ≤ q) :
    ∃ Q : GAP (ZMod q), (Q + Q).Proper ∧ X ⊆ Q.carrier ∧ Q.dim ≤ 2 * κ - 1 ∧
      #Q.carrier ≤ Real.exp (10 ^ 30 * κ ^ 7) * #X :=
  sorry

end ChangFreimanRuzsa
