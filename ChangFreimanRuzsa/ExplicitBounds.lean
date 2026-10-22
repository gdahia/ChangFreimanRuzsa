/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GeneralizedArithmeticProgression
public import Mathlib.Analysis.Complex.Exponential
public import SumOfSetsInSeveralDimensions.FreimanDimension
import ChangFreimanRuzsa.Bound
import ChangFreimanRuzsa.CyclicFreimanDimension
import SumOfSetsInSeveralDimensions.FreimanDimensionSumsetBounds

/-!
# Chang's theorem with explicit bounds

Chang's theorem for finite sets of integers and for subsets of `ZMod q` with `q` prime, with the
exponents in `exists_twoProperGAP_int_dim_le_freimanDim` and
`exists_twoProperGAP_zmod_dim_le_freimanDim` replaced by the polynomial bounds of
`ChangFreimanRuzsa.Bound` and `ChangFreimanRuzsa.CyclicFreimanDimension`. For `2 ≤ κ`, a set `X`
with `#(X + X) ≤ κ * #X` lies in a `2`-proper progression of dimension at most `freimanDim X` with
at most `exp (C * κ ^ 7) * #X` points, for an absolute constant `C`. The Freiman dimension of `X`
is at most `2 * κ - 1`, so the progression has dimension at most `2 * κ - 1`.

## Main statements

* `exists_twoProperGAP_subset_dim_le_freimanDim_card_le`: the explicit form for sets of integers,
  with dimension at most `freimanDim X`.
* `exists_twoProperGAP_zmod_subset_dim_le_freimanDim_card_le`: the explicit form in `ZMod q`, with
  dimension at most `freimanDim X`.
* `exists_twoProperGAP_subset_dim_le_card_le`: the explicit form for sets of integers, with
  dimension at most `2 * κ - 1`.
* `exists_twoProperGAP_zmod_subset_dim_le_card_le`: the explicit form in `ZMod q`, with dimension
  at most `2 * κ - 1`.
-/

public section

open Finset SumOfSetsInSeveralDimensions
open scoped Pointwise

namespace ChangFreimanRuzsa

/-- **Chang's theorem** for sets of integers, with the dimension bounded by the Freiman dimension. A
finite nonempty set `X` of integers with `#(X + X) ≤ κ * #X`, where `2 ≤ κ`, is contained in a
`2`-proper generalized arithmetic progression of dimension at most `freimanDim X` with at most
`Real.exp (10 ^ 32 * κ ^ 7) * #X` points. -/
theorem exists_twoProperGAP_subset_dim_le_freimanDim_card_le {κ : ℝ} (X : Finset ℤ)
    (hX : X.Nonempty) (hκ : 2 ≤ κ) (hXX : (#(X + X) : ℝ) ≤ κ * #X) :
    ∃ P : GAP ℤ, P.TwoProper ∧ X ⊆ P.carrier ∧ P.dim ≤ freimanDim X ∧
      (#P.carrier : ℝ) ≤ Real.exp (10 ^ 32 * κ ^ 7) * #X := by
  obtain ⟨P, hP, hXP, hdim, hcard⟩ := exists_twoProperGAP_int_dim_le_freimanDim X hX hκ hXX
  refine ⟨P, hP, hXP, hdim, hcard.trans ?_⟩
  grw [intFreimanDimExponent_le hκ]

/-- **Chang's theorem** in `ZMod q` for a prime `q`, with the dimension bounded by the Freiman
dimension. A set `X` with `#(X + X) ≤ κ * #X`, where `2 ≤ κ`, with at least
`7 * 10 ^ 7 * κ ^ 2` elements and with `Real.exp (10 ^ 30 * κ ^ 7) * #X ≤ q`, is contained in a
`2`-proper generalized arithmetic progression of dimension at most `freimanDim X` with at most
`Real.exp (10 ^ 30 * κ ^ 7) * #X` points. -/
theorem exists_twoProperGAP_zmod_subset_dim_le_freimanDim_card_le {q : ℕ} {κ : ℝ}
    (X : Finset (ZMod q)) (hq : q.Prime) (hκ : 2 ≤ κ) (hXX : (#(X + X) : ℝ) ≤ κ * #X)
    (hXlower : 7 * 10 ^ 7 * κ ^ 2 ≤ #X)
    (hXupper : Real.exp (10 ^ 30 * κ ^ 7) * #X ≤ q) :
    ∃ Q : GAP (ZMod q), Q.TwoProper ∧ X ⊆ Q.carrier ∧ Q.dim ≤ freimanDim X ∧
      (#Q.carrier : ℝ) ≤ Real.exp (10 ^ 30 * κ ^ 7) * #X := by
  have he : Real.exp (freimanDimExponent κ) * #X ≤ Real.exp (10 ^ 30 * κ ^ 7) * #X := by
    grw [freimanDimExponent_le hκ]
  obtain ⟨Q, hQ, hXQ, hdim, hcard⟩ := exists_twoProperGAP_zmod_dim_le_freimanDim X hq hκ hXX
    ((mul_bohrGAPDim_le hκ).trans hXlower) (he.trans hXupper)
  exact ⟨Q, hQ, hXQ, hdim, hcard.trans he⟩

/-- **Chang's theorem** for sets of integers. A finite nonempty set `X` of integers with
`#(X + X) ≤ κ * #X`, where `2 ≤ κ`, is contained in a `2`-proper generalized arithmetic
progression of dimension at most `2 * κ - 1` with at most `Real.exp (10 ^ 32 * κ ^ 7) * #X`
points. The Freiman dimension of `X` is at most `2 * κ - 1`. -/
theorem exists_twoProperGAP_subset_dim_le_card_le {κ : ℝ} (X : Finset ℤ) (hX : X.Nonempty)
    (hκ : 2 ≤ κ) (hXX : (#(X + X) : ℝ) ≤ κ * #X) :
    ∃ P : GAP ℤ, P.TwoProper ∧ X ⊆ P.carrier ∧ (P.dim : ℝ) ≤ 2 * κ - 1 ∧
      (#P.carrier : ℝ) ≤ Real.exp (10 ^ 32 * κ ^ 7) * #X := by
  obtain ⟨P, hP, hXP, hdim, hcard⟩ :=
    exists_twoProperGAP_subset_dim_le_freimanDim_card_le X hX hκ hXX
  exact ⟨P, hP, hXP,
    (Nat.cast_le.2 hdim).trans (freimanDim_le_two_mul_sub_one_of_card_add_le hX hXX), hcard⟩

/-- **Chang's theorem** in `ZMod q` for a prime `q`. A set `X` with `#(X + X) ≤ κ * #X`, where
`2 ≤ κ`, with at least `7 * 10 ^ 7 * κ ^ 2` elements and with
`Real.exp (10 ^ 30 * κ ^ 7) * #X ≤ q`, is contained in a `2`-proper generalized arithmetic
progression of dimension at most `2 * κ - 1` with at most `Real.exp (10 ^ 30 * κ ^ 7) * #X`
points. The Freiman dimension of `X` is at most `2 * κ - 1`. -/
theorem exists_twoProperGAP_zmod_subset_dim_le_card_le {q : ℕ} {κ : ℝ} (X : Finset (ZMod q))
    (hq : q.Prime) (hκ : 2 ≤ κ) (hXX : (#(X + X) : ℝ) ≤ κ * #X)
    (hXlower : 7 * 10 ^ 7 * κ ^ 2 ≤ #X)
    (hXupper : Real.exp (10 ^ 30 * κ ^ 7) * #X ≤ q) :
    ∃ Q : GAP (ZMod q), Q.TwoProper ∧ X ⊆ Q.carrier ∧ (Q.dim : ℝ) ≤ 2 * κ - 1 ∧
      (#Q.carrier : ℝ) ≤ Real.exp (10 ^ 30 * κ ^ 7) * #X := by
  obtain ⟨Q, hQ, hXQ, hdim, hcard⟩ :=
    exists_twoProperGAP_zmod_subset_dim_le_freimanDim_card_le X hq hκ hXX hXlower hXupper
  exact ⟨Q, hQ, hXQ, (Nat.cast_le.2 hdim).trans (freimanDim_le_two_mul_sub_one_of_card_add_le
    (nonempty_of_mul_bohrGAPDim_le ((mul_bohrGAPDim_le hκ).trans hXlower)) hXX), hcard⟩

end ChangFreimanRuzsa
