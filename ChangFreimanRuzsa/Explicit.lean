/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GAP.Basic
public import Mathlib.Analysis.Complex.Exponential
public import SumOfSetsInSeveralDimensions.FreimanDimension
import ChangFreimanRuzsa.ExponentBounds
import ChangFreimanRuzsa.FreimanDim
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import SumOfSetsInSeveralDimensions.FreimanDimensionSumsetBounds

/-!
# Chang's theorem with explicit bounds

Chang's theorem for finite sets of integers and for subsets of `ZMod q` with `q` prime, with the
exponents in `exists_twoProperGAP_int_dim_le_freimanDim` and
`exists_twoProperGAP_zmod_dim_le_freimanDim` replaced by the polynomial bounds of
`ChangFreimanRuzsa.ExponentBounds` and `ChangFreimanRuzsa.FreimanDim`. For `2 ≤ κ`, a set `X`
with `#(X + X) ≤ κ * #X` lies in a `2`-proper progression of dimension at most `freimanDim X` with
at most `exp (C * κ ^ 7) * #X` points, for an absolute constant `C`. The Freiman dimension of `X`
is at most `2 * κ - 1`, so the progression has dimension at most `2 * κ - 1`. It is also at most
`κ - 1 + κ * (2 * κ - 1) / #X`, so the progression has dimension at most `⌊κ - 1 + ε⌋₊` when
`κ * (2 * κ - 1) ≤ ε * #X`, as in Green and Tao.

The file also gives the Bogolyubov–Ruzsa lemma with explicit bounds, the first step of the proof:
if moreover `7 * 10 ^ 7 * κ ^ 2 ≤ #X`, then `X + X - (X + X)` contains a proper progression of
dimension at most `3 * 10 ^ 5 * κ ^ 2` with at least `#X / exp (2 * 10 ^ 7 * κ ^ 2)` points.

## Main statements

* `exists_proper_gap_subset_add_sub_add_dim_le_card_le`: the Bogolyubov–Ruzsa lemma for sets of
  integers.
* `exists_proper_gap_zmod_subset_add_sub_add_dim_le_card_le`: the Bogolyubov–Ruzsa lemma in
  `ZMod q`.
* `exists_twoProperGAP_subset_dim_le_freimanDim_card_le`: the explicit form for sets of integers,
  with dimension at most `freimanDim X`.
* `exists_twoProperGAP_zmod_subset_dim_le_freimanDim_card_le`: the explicit form in `ZMod q`, with
  dimension at most `freimanDim X`.
* `exists_twoProperGAP_subset_dim_le_card_le`: the explicit form for sets of integers, with
  dimension at most `2 * κ - 1`.
* `exists_twoProperGAP_zmod_subset_dim_le_card_le`: the explicit form in `ZMod q`, with dimension
  at most `2 * κ - 1`.
* `exists_twoProperGAP_subset_dim_le_floor_card_le`: the explicit form for sets of integers with
  `κ * (2 * κ - 1) ≤ ε * #X`, with dimension at most `⌊κ - 1 + ε⌋₊`.
* `exists_twoProperGAP_zmod_subset_dim_le_floor_card_le`: the explicit form in `ZMod q` with
  `κ * (2 * κ - 1) ≤ ε * #X`, with dimension at most `⌊κ - 1 + ε⌋₊`.
-/

public section

open Finset SumOfSetsInSeveralDimensions
open scoped Pointwise

namespace ChangFreimanRuzsa

/-- **Bogolyubov–Ruzsa lemma** for sets of integers. If a finite set `X` of integers satisfies
`#(X + X) ≤ κ * #X`, where `2 ≤ κ`, and has at least `7 * 10 ^ 7 * κ ^ 2` elements, then
`X + X - (X + X)` contains a proper generalized arithmetic progression `Q` of dimension at most
`3 * 10 ^ 5 * κ ^ 2` with `#X ≤ Real.exp (2 * 10 ^ 7 * κ ^ 2) * #Q.carrier`. -/
theorem exists_proper_gap_subset_add_sub_add_dim_le_card_le {κ : ℝ} (X : Finset ℤ) (hκ : 2 ≤ κ)
    (hXX : #(X + X) ≤ κ * #X) (hXlower : 7 * 10 ^ 7 * κ ^ 2 ≤ #X) :
    ∃ Q : GAP ℤ, Q.Proper ∧ Q.carrier ⊆ X + X - (X + X) ∧ Q.dim ≤ 3 * 10 ^ 5 * κ ^ 2 ∧
      #X ≤ Real.exp (2 * 10 ^ 7 * κ ^ 2) * #Q.carrier := by
  obtain ⟨-, Q, -, -, hQ, hdim, hsub, hcard⟩ := exists_proper_gap_int_subset_add_sub_add_card_le X
    hκ hXX ((mul_bohrGAPDim_le hκ).trans hXlower)
  refine ⟨Q, hQ, hsub, by linarith [mul_bohrGAPDim_le hκ], hcard.trans ?_⟩
  grw [mul_bohrLoss_bohrGAPDim_le hκ]

/-- **Bogolyubov–Ruzsa lemma** in `ZMod q` for a prime `q`. If a set `X` satisfies
`#(X + X) ≤ κ * #X`, where `2 ≤ κ`, and has at least `7 * 10 ^ 7 * κ ^ 2` elements, then
`X + X - (X + X)` contains a proper generalized arithmetic progression `Q` of dimension at most
`3 * 10 ^ 5 * κ ^ 2` with `#X ≤ Real.exp (2 * 10 ^ 7 * κ ^ 2) * #Q.carrier`. -/
theorem exists_proper_gap_zmod_subset_add_sub_add_dim_le_card_le {q : ℕ} {κ : ℝ}
    (X : Finset (ZMod q)) (hq : q.Prime) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X)
    (hXlower : 7 * 10 ^ 7 * κ ^ 2 ≤ #X) :
    ∃ Q : GAP (ZMod q), Q.Proper ∧ Q.carrier ⊆ X + X - (X + X) ∧ Q.dim ≤ 3 * 10 ^ 5 * κ ^ 2 ∧
      #X ≤ Real.exp (2 * 10 ^ 7 * κ ^ 2) * #Q.carrier := by
  obtain ⟨-, Q, -, -, hQ, hdim, hsub, hcard⟩ := exists_proper_gap_zmod_subset_add_sub_add_card_le X
    hq hκ hXX ((mul_bohrGAPDim_le hκ).trans hXlower)
  refine ⟨Q, hQ, hsub, by linarith [mul_bohrGAPDim_le hκ], hcard.trans ?_⟩
  grw [mul_bohrLoss_bohrGAPDim_le hκ]

/-- **Chang's theorem** for sets of integers, with the dimension bounded by the Freiman dimension. A
finite nonempty set `X` of integers with `#(X + X) ≤ κ * #X`, where `2 ≤ κ`, is contained in a
`2`-proper generalized arithmetic progression of dimension at most `freimanDim X` with at most
`Real.exp (10 ^ 32 * κ ^ 7) * #X` points. -/
theorem exists_twoProperGAP_subset_dim_le_freimanDim_card_le {κ : ℝ} (X : Finset ℤ)
    (hX : X.Nonempty) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X) :
    ∃ P : GAP ℤ, (P + P).Proper ∧ X ⊆ P.carrier ∧ P.dim ≤ freimanDim X ∧
      #P.carrier ≤ Real.exp (10 ^ 32 * κ ^ 7) * #X := by
  obtain ⟨P, hP, hXP, hdim, hcard⟩ := exists_twoProperGAP_int_dim_le_freimanDim X hX hκ hXX
  refine ⟨P, hP, hXP, hdim, hcard.trans ?_⟩
  grw [intFreimanDimExponent_le hκ]

/-- **Chang's theorem** in `ZMod q` for a prime `q`, with the dimension bounded by the Freiman
dimension. A set `X` with `#(X + X) ≤ κ * #X`, where `2 ≤ κ`, with at least
`7 * 10 ^ 7 * κ ^ 2` elements and with `Real.exp (10 ^ 30 * κ ^ 7) * #X ≤ q`, is contained in a
`2`-proper generalized arithmetic progression of dimension at most `freimanDim X` with at most
`Real.exp (10 ^ 30 * κ ^ 7) * #X` points. -/
theorem exists_twoProperGAP_zmod_subset_dim_le_freimanDim_card_le {q : ℕ} {κ : ℝ}
    (X : Finset (ZMod q)) (hq : q.Prime) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X)
    (hXlower : 7 * 10 ^ 7 * κ ^ 2 ≤ #X) (hXupper : Real.exp (10 ^ 30 * κ ^ 7) * #X ≤ q) :
    ∃ Q : GAP (ZMod q), (Q + Q).Proper ∧ X ⊆ Q.carrier ∧ Q.dim ≤ freimanDim X ∧
      #Q.carrier ≤ Real.exp (10 ^ 30 * κ ^ 7) * #X := by
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
    (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X) :
    ∃ P : GAP ℤ, (P + P).Proper ∧ X ⊆ P.carrier ∧ P.dim ≤ 2 * κ - 1 ∧
      #P.carrier ≤ Real.exp (10 ^ 32 * κ ^ 7) * #X := by
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
    (hq : q.Prime) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X) (hXlower : 7 * 10 ^ 7 * κ ^ 2 ≤ #X)
    (hXupper : Real.exp (10 ^ 30 * κ ^ 7) * #X ≤ q) :
    ∃ Q : GAP (ZMod q), (Q + Q).Proper ∧ X ⊆ Q.carrier ∧ Q.dim ≤ 2 * κ - 1 ∧
      #Q.carrier ≤ Real.exp (10 ^ 30 * κ ^ 7) * #X := by
  obtain ⟨Q, hQ, hXQ, hdim, hcard⟩ :=
    exists_twoProperGAP_zmod_subset_dim_le_freimanDim_card_le X hq hκ hXX hXlower hXupper
  exact ⟨Q, hQ, hXQ, (Nat.cast_le.2 hdim).trans (freimanDim_le_two_mul_sub_one_of_card_add_le
    (nonempty_of_mul_bohrGAPDim_le ((mul_bohrGAPDim_le hκ).trans hXlower)) hXX), hcard⟩

/-- If `#(X + X) ≤ κ * #X` and `κ * (2 * κ - 1) ≤ ε * #X` for a nonempty `X`, then `X` has
Freiman dimension at most `⌊κ - 1 + ε⌋₊`. -/
lemma freimanDim_le_floor_sub_one_add_of_card_add_le {G : Type*} [DecidableEq G]
    [AddCancelCommMonoid G] {κ ε : ℝ} {X : Finset G} (hX : X.Nonempty)
    (hXX : #(X + X) ≤ κ * #X) (hXε : κ * (2 * κ - 1) ≤ ε * #X) :
    freimanDim X ≤ ⌊κ - 1 + ε⌋₊ := by
  refine Nat.le_floor ((freimanDim_le_sub_one_add_mul_div_card_of_card_add_le hX hXX).trans ?_)
  gcongr
  rwa [div_le_iff₀ (mod_cast hX.card_pos)]

/-- **Chang's theorem** for sets of integers, with the dimension bound of Green and Tao. A finite
set `X` of integers with `#(X + X) ≤ κ * #X`, where `2 ≤ κ`, and with `κ * (2 * κ - 1) ≤ ε * #X`
is contained in a `2`-proper generalized arithmetic progression of dimension at most
`⌊κ - 1 + ε⌋₊` with at most `Real.exp (10 ^ 32 * κ ^ 7) * #X` points. -/
theorem exists_twoProperGAP_subset_dim_le_floor_card_le {κ ε : ℝ} (X : Finset ℤ) (hκ : 2 ≤ κ)
    (hXX : #(X + X) ≤ κ * #X) (hXε : κ * (2 * κ - 1) ≤ ε * #X) :
    ∃ P : GAP ℤ, (P + P).Proper ∧ X ⊆ P.carrier ∧ P.dim ≤ ⌊κ - 1 + ε⌋₊ ∧
      #P.carrier ≤ Real.exp (10 ^ 32 * κ ^ 7) * #X := by
  obtain rfl | hX := X.eq_empty_or_nonempty
  · simp at hXε
    nlinarith
  obtain ⟨P, hP, hXP, hdim, hcard⟩ :=
    exists_twoProperGAP_subset_dim_le_freimanDim_card_le X hX hκ hXX
  exact ⟨P, hP, hXP, hdim.trans (freimanDim_le_floor_sub_one_add_of_card_add_le hX hXX hXε),
    hcard⟩

/-- **Chang's theorem** in `ZMod q` for a prime `q`, with the dimension bound of Green and Tao. A
set `X` with `#(X + X) ≤ κ * #X`, where `2 ≤ κ`, with at least `7 * 10 ^ 7 * κ ^ 2` elements, with
`Real.exp (10 ^ 30 * κ ^ 7) * #X ≤ q` and with `κ * (2 * κ - 1) ≤ ε * #X` is contained in a
`2`-proper generalized arithmetic progression of dimension at most `⌊κ - 1 + ε⌋₊` with at most
`Real.exp (10 ^ 30 * κ ^ 7) * #X` points. -/
theorem exists_twoProperGAP_zmod_subset_dim_le_floor_card_le {q : ℕ} {κ ε : ℝ}
    (X : Finset (ZMod q)) (hq : q.Prime) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X)
    (hXlower : 7 * 10 ^ 7 * κ ^ 2 ≤ #X) (hXupper : Real.exp (10 ^ 30 * κ ^ 7) * #X ≤ q)
    (hXε : κ * (2 * κ - 1) ≤ ε * #X) :
    ∃ Q : GAP (ZMod q), (Q + Q).Proper ∧ X ⊆ Q.carrier ∧ Q.dim ≤ ⌊κ - 1 + ε⌋₊ ∧
      #Q.carrier ≤ Real.exp (10 ^ 30 * κ ^ 7) * #X := by
  obtain ⟨Q, hQ, hXQ, hdim, hcard⟩ :=
    exists_twoProperGAP_zmod_subset_dim_le_freimanDim_card_le X hq hκ hXX hXlower hXupper
  exact ⟨Q, hQ, hXQ, hdim.trans (freimanDim_le_floor_sub_one_add_of_card_add_le
    (nonempty_of_mul_bohrGAPDim_le ((mul_bohrGAPDim_le hκ).trans hXlower)) hXX hXε), hcard⟩

end ChangFreimanRuzsa
