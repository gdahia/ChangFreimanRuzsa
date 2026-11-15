/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Pi.Interval
public import Mathlib.Data.Nat.Prime.Defs

/-!
# Chang's theorem

Chang's polynomial form of Freiman's theorem for finite sets of integers and for subsets of
`ZMod q` with `q` prime: for every `2 ≤ t`, a set with small doubling lies in a `t`-proper
generalized arithmetic progression of comparable size. Also the Bogolyubov–Ruzsa lemma, the first
step of its proof: for such a set `X`, the set `2 • X - 2 • X` contains a large proper generalized
arithmetic progression.

A generalized arithmetic progression has a dimension `dim`, an `origin`, steps `step i` and bounds
`bound i` for `i : Fin dim`, and its points are `origin + ∑ i, w i • step i` with `w ≤ bound`. It
coerces to the finset of its points. It is `t`-proper when `t • P`, with origin `t • origin`, the
same steps and bound `t • bound`, is proper.

The proofs are in `Solution.lean`.
-/

@[expose] public section

open Finset
open scoped Pointwise

namespace ChangFreimanRuzsa

noncomputable section

/-- A generalized arithmetic progression, not necessarily proper: the set of the points
`origin + ∑ i, w i • step i` with `w ≤ bound`. -/
structure GAP (G : Type*) [AddCommMonoid G] where
  /-- The number of steps. -/
  dim : ℕ
  /-- The base point. -/
  origin : G
  /-- The steps. -/
  step : Fin dim → G
  /-- The largest coefficient of each step. The length of the step `i` is `bound i + 1`. -/
  bound : Fin dim → ℕ

namespace GAP

variable {G : Type*} [AddCommMonoid G]

/-- The point `origin + ∑ i, w i • step i`. -/
def eval (P : GAP G) (w : Fin P.dim → ℕ) : G := P.origin + ∑ i, w i • P.step i

/-- The set of points of a progression. -/
@[coe] def toFinset [DecidableEq G] (P : GAP G) : Finset G := (Finset.Iic P.bound).image P.eval

instance [DecidableEq G] : CoeOut (GAP G) (Finset G) := ⟨toFinset⟩

/-- A progression is proper if the points `origin + ∑ i, w i • step i` with `w ≤ bound` are
distinct. -/
def Proper (P : GAP G) : Prop := Set.InjOn P.eval (Set.Iic P.bound)

/-- The multiple `t • P` of a progression multiplies the origin and the bound by `t`. A progression
`P` is `t`-proper when `t • P` is proper. -/
instance : SMul ℕ (GAP G) where
  smul t P := ⟨P.dim, t • P.origin, P.step, t • P.bound⟩

end GAP

end

/-- **Bogolyubov–Ruzsa lemma** for sets of integers, with the bounds of Chang. If a finite nonempty
set `X` of integers satisfies `#(X + X) ≤ κ * #X`, where `2 ≤ κ`, then `2 • X - 2 • X` contains a
proper generalized arithmetic progression `Q` of dimension at most
`3 * 10 ^ 5 * κ * (1 + Real.log κ)` with
`#X ≤ Real.exp (2 * 10 ^ 7 * κ * (1 + Real.log κ) ^ 2) * #(Q : Finset ℤ)`. -/
theorem exists_proper_gap_subset_nsmul_sub_nsmul_dim_le_card_le' {κ : ℝ} (X : Finset ℤ)
    (hX : X.Nonempty) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X) :
    ∃ Q : GAP ℤ, Q.Proper ∧ (Q : Finset ℤ) ⊆ 2 • X - 2 • X ∧
      Q.dim ≤ 3 * 10 ^ 5 * κ * (1 + Real.log κ) ∧
      #X ≤ Real.exp (2 * 10 ^ 7 * κ * (1 + Real.log κ) ^ 2) * #(Q : Finset ℤ) :=
  sorry

/-- **Bogolyubov–Ruzsa lemma** in `ZMod q` for a prime `q`, with the bounds of Chang. If a nonempty
set `X` satisfies `#(X + X) ≤ κ * #X`, where `2 ≤ κ`, then `2 • X - 2 • X` contains a proper
generalized arithmetic progression `Q` of dimension at most `3 * 10 ^ 5 * κ * (1 + Real.log κ)`
with `#X ≤ Real.exp (2 * 10 ^ 7 * κ * (1 + Real.log κ) ^ 2) * #(Q : Finset (ZMod q))`. -/
theorem exists_proper_gap_zmod_subset_nsmul_sub_nsmul_dim_le_card_le' {q : ℕ} {κ : ℝ}
    (X : Finset (ZMod q)) (hq : q.Prime) (hX : X.Nonempty) (hκ : 2 ≤ κ)
    (hXX : #(X + X) ≤ κ * #X) :
    ∃ Q : GAP (ZMod q), Q.Proper ∧ (Q : Finset (ZMod q)) ⊆ 2 • X - 2 • X ∧
      Q.dim ≤ 3 * 10 ^ 5 * κ * (1 + Real.log κ) ∧
      #X ≤ Real.exp (2 * 10 ^ 7 * κ * (1 + Real.log κ) ^ 2) * #(Q : Finset (ZMod q)) :=
  sorry

/-- **Chang's theorem** for sets of integers. Let `2 ≤ t`. A finite nonempty set `X` of integers
with `#(X + X) ≤ κ * #X`, where `2 ≤ κ`, is contained in a `t`-proper generalized arithmetic
progression of dimension at most `2 * κ - 1` with at most
`Real.exp (2 * 10 ^ 11 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X` points. -/
theorem exists_tProperGAP_subset_dim_le_card_le' {t : ℕ} {κ : ℝ} (X : Finset ℤ) (hX : X.Nonempty)
    (ht : 2 ≤ t) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X) :
    ∃ P : GAP ℤ, (t • P).Proper ∧ X ⊆ P ∧ P.dim ≤ 2 * κ - 1 ∧
      #(P : Finset ℤ) ≤
        Real.exp (2 * 10 ^ 11 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X :=
  sorry

/-- **Chang's theorem** in `ZMod q` for a prime `q`. Let `2 ≤ t`. A set `X` with
`#(X + X) ≤ κ * #X`, where `2 ≤ κ`, with at least `7 * 10 ^ 7 * κ ^ 2` elements and with
`Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X ≤ q`, is contained in a
`t`-proper generalized arithmetic progression of dimension at most `2 * κ - 1` with at most
`Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X` points. -/
theorem exists_tProperGAP_zmod_subset_dim_le_card_le' {q t : ℕ} {κ : ℝ} (X : Finset (ZMod q))
    (hq : q.Prime) (ht : 2 ≤ t) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X)
    (hXlower : 7 * 10 ^ 7 * κ ^ 2 ≤ #X)
    (hXupper : Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X ≤ q) :
    ∃ Q : GAP (ZMod q), (t • Q).Proper ∧ X ⊆ Q ∧ Q.dim ≤ 2 * κ - 1 ∧
      #(Q : Finset (ZMod q)) ≤
        Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X :=
  sorry

/-- **Chang's theorem** for sets of integers, with the dimension bound of Green and Tao. Let
`2 ≤ t`. A finite set `X` of integers with `#(X + X) ≤ κ * #X`, where `2 ≤ κ`, and with
`κ * (2 * κ - 1) ≤ ε * #X` is contained in a `t`-proper generalized arithmetic progression of
dimension at most `⌊κ - 1 + ε⌋₊` with at most
`Real.exp (2 * 10 ^ 11 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X` points. -/
theorem exists_tProperGAP_subset_dim_le_floor_card_le' {t : ℕ} {κ ε : ℝ} (X : Finset ℤ) (ht : 2 ≤ t)
    (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X) (hXε : κ * (2 * κ - 1) ≤ ε * #X) :
    ∃ P : GAP ℤ, (t • P).Proper ∧ X ⊆ P ∧ P.dim ≤ ⌊κ - 1 + ε⌋₊ ∧
      #(P : Finset ℤ) ≤
        Real.exp (2 * 10 ^ 11 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X :=
  sorry

/-- **Chang's theorem** in `ZMod q` for a prime `q`, with the dimension bound of Green and Tao. Let
`2 ≤ t`. A set `X` with `#(X + X) ≤ κ * #X`, where `2 ≤ κ`, with at least `7 * 10 ^ 7 * κ ^ 2`
elements, with `Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X ≤ q`
and with `κ * (2 * κ - 1) ≤ ε * #X` is contained in a `t`-proper generalized arithmetic progression
of dimension at most `⌊κ - 1 + ε⌋₊` with at most
`Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X` points. -/
theorem exists_tProperGAP_zmod_subset_dim_le_floor_card_le' {q t : ℕ} {κ ε : ℝ}
    (X : Finset (ZMod q)) (hq : q.Prime) (ht : 2 ≤ t) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X)
    (hXlower : 7 * 10 ^ 7 * κ ^ 2 ≤ #X)
    (hXupper : Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X ≤ q)
    (hXε : κ * (2 * κ - 1) ≤ ε * #X) :
    ∃ Q : GAP (ZMod q), (t • Q).Proper ∧ X ⊆ Q ∧ Q.dim ≤ ⌊κ - 1 + ε⌋₊ ∧
      #(Q : Finset (ZMod q)) ≤
        Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X :=
  sorry

end ChangFreimanRuzsa
