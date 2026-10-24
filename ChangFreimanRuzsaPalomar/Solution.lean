/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Finsupp.Interval
public import Mathlib.Data.Nat.Prime.Defs
public import ChangFreimanRuzsa.GeneralizedArithmeticProgression
import ChangFreimanRuzsa.ExplicitBounds

/-!
# Chang's theorem

The statements of `Challenge.lean`, which are the results of the library with the same names
without the prime. The definitions `GAP`, `GAP.eval`, `GAP.carrier`, `GAP.dim`, `GAP.Proper` and
the sum of two progressions are those of the library.
-/

public section

open Finset
open scoped Pointwise

namespace ChangFreimanRuzsa

/-- **Chang's theorem** for sets of integers. A finite nonempty set `X` of integers with
`#(X + X) ≤ κ * #X`, where `2 ≤ κ`, is contained in a `2`-proper generalized arithmetic
progression of dimension at most `2 * κ - 1` with at most `Real.exp (10 ^ 32 * κ ^ 7) * #X`
points. -/
theorem exists_twoProperGAP_subset_dim_le_card_le' {κ : ℝ} (X : Finset ℤ) (hX : X.Nonempty)
    (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X) :
    ∃ P : GAP ℤ, (P + P).Proper ∧ X ⊆ P.carrier ∧ P.dim ≤ 2 * κ - 1 ∧
      #P.carrier ≤ Real.exp (10 ^ 32 * κ ^ 7) * #X :=
  exists_twoProperGAP_subset_dim_le_card_le X hX hκ hXX

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
  exists_twoProperGAP_zmod_subset_dim_le_card_le X hq hκ hXX hXlower hXupper

end ChangFreimanRuzsa
