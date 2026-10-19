/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib

/-!
# Chang's theorem

Chang's polynomial form of Freiman's theorem, with the $2$-proper progression of Green and Tao, for
finite sets of integers and for subsets of `ZMod q` with $q$ prime: a set with small doubling lies
in a $2$-proper generalized arithmetic progression of comparable size.

A generalized arithmetic progression of dimension $d$ consists of the points
$a + \sum_i w_i s_i$ with $0 \le w_i < \ell_i$ for each $i < d$. It is $2$-proper when the points
$2a + \sum_i w_i s_i$ with $0 \le w_i < 2 \ell_i$ are distinct.

The proofs are in `Solution.lean`.
-/

@[expose] public section

open Finset
open scoped Pointwise

namespace ChangFreimanRuzsa

/-- The point `origin + ∑ i, w i • step i`. -/
def gapMap {G : Type*} [AddCommMonoid G] {d : ℕ} (origin : G) (step : Fin d → G)
    (length : Fin d → ℕ) (w : (i : Fin d) → Fin (length i)) : G := origin + ∑ i, (w i : ℕ) • step i

/-- A generalized arithmetic progression, not necessarily proper: the set of the points
`origin + ∑ i, w i • step i` with `w i < length i`. -/
structure GAP (G : Type*) [DecidableEq G] [AddCommMonoid G] where
  /-- The dimension. -/
  dim : ℕ
  /-- The set of points. -/
  carrier : Finset G
  /-- The base point. -/
  origin : G
  /-- The steps. -/
  step : Fin dim → G
  /-- The side lengths. -/
  length : Fin dim → ℕ
  length_pos : ∀ i, 0 < length i
  carrier_eq : carrier = Finset.univ.image (gapMap origin step length)

/-- A progression is `2`-proper if the points of the progression with doubled origin and doubled
lengths are distinct. -/
def GAP.TwoProper {G : Type*} [DecidableEq G] [AddCommMonoid G] (P : GAP G) : Prop :=
  Function.Injective (gapMap (2 • P.origin) P.step (fun i ↦ 2 * P.length i))

/-- **Chang's theorem** for sets of integers. A finite nonempty set $X$ of integers with
$|X + X| \le \kappa |X|$, where $\kappa \ge 2$, is contained in a $2$-proper generalized
arithmetic progression of dimension at most $3 \cdot 10^{14} \kappa^5$ with at most
$\exp(10^{59} \kappa^{20}) |X|$ points. -/
theorem exists_twoProperGAP_subset_dim_le_card_le' {κ : ℝ} (X : Finset ℤ) (hX : X.Nonempty)
    (hκ : 2 ≤ κ) (hXX : (#(X + X) : ℝ) ≤ κ * #X) :
    ∃ P : GAP ℤ, P.TwoProper ∧ X ⊆ P.carrier ∧ (P.dim : ℝ) ≤ 3 * 10 ^ 14 * κ ^ 5 ∧
      (#P.carrier : ℝ) ≤ Real.exp (10 ^ 59 * κ ^ 20) * #X :=
  sorry

/-- **Chang's theorem** in `ZMod q` for a prime $q$. A set $X$ with $|X + X| \le \kappa |X|$,
where $\kappa \ge 2$, with more than $\exp(7 \cdot 10^{12} \kappa^5)$ elements and with
$\exp(10^{53} \kappa^{20}) |X| \le q$, is contained in a $2$-proper generalized arithmetic
progression of dimension at most $7 \cdot 10^{12} \kappa^5$ with at most
$\exp(10^{53} \kappa^{20}) |X|$ points. -/
theorem exists_twoProperGAP_zmod_subset_dim_le_card_le' {q : ℕ} {κ : ℝ} (X : Finset (ZMod q))
    (hq : q.Prime) (hκ : 2 ≤ κ) (hXX : (#(X + X) : ℝ) ≤ κ * #X)
    (hXlower : Real.exp (7 * 10 ^ 12 * κ ^ 5) < #X)
    (hXupper : Real.exp (10 ^ 53 * κ ^ 20) * #X ≤ q) :
    ∃ Q : GAP (ZMod q), Q.TwoProper ∧ X ⊆ Q.carrier ∧ (Q.dim : ℝ) ≤ 7 * 10 ^ 12 * κ ^ 5 ∧
      (#Q.carrier : ℝ) ≤ Real.exp (10 ^ 53 * κ ^ 20) * #X :=
  sorry

end ChangFreimanRuzsa
