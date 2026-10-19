/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.ExplicitBounds

/-!
# Chang's theorem

The statements of `Challenge.lean`, which are the results of the library with the same names
without the prime. The definitions `gapMap`, `GAP` and `GAP.TwoProper` are those of the library.
-/

public section

open Finset
open scoped Pointwise

namespace ChangFreimanRuzsa

/-- **Chang's theorem** for sets of integers. A finite nonempty set $X$ of integers with
$|X + X| \le \kappa |X|$, where $\kappa \ge 2$, is contained in a $2$-proper generalized
arithmetic progression of dimension at most $3 \cdot 10^{14} \kappa^5$ with at most
$\exp(10^{59} \kappa^{20}) |X|$ points. -/
theorem exists_twoProperGAP_subset_dim_le_card_le' {κ : ℝ} (X : Finset ℤ) (hX : X.Nonempty)
    (hκ : 2 ≤ κ) (hXX : (#(X + X) : ℝ) ≤ κ * #X) :
    ∃ P : GAP ℤ, P.TwoProper ∧ X ⊆ P.carrier ∧ (P.dim : ℝ) ≤ 3 * 10 ^ 14 * κ ^ 5 ∧
      (#P.carrier : ℝ) ≤ Real.exp (10 ^ 59 * κ ^ 20) * #X :=
  exists_twoProperGAP_subset_dim_le_card_le X hX hκ hXX

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
  exists_twoProperGAP_zmod_subset_dim_le_card_le X hq hκ hXX hXlower hXupper

end ChangFreimanRuzsa
