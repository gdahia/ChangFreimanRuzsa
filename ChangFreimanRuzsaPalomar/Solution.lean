/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Finsupp.Interval
public import Mathlib.Data.Nat.Prime.Defs
public import ChangFreimanRuzsa.GAP.Basic
import ChangFreimanRuzsa.Explicit

/-!
# Chang's theorem and the Bogolyubov–Ruzsa lemma

The statements of `Challenge.lean`, which are the results of the library with the same names
without the prime. The definitions `GAP`, `GAP.eval`, `GAP.carrier`, `GAP.dim`, `GAP.Proper` and
the sum of two progressions are those of the library.
-/

public section

open Finset
open scoped Pointwise

namespace ChangFreimanRuzsa

/-- **Bogolyubov–Ruzsa lemma** for sets of integers. If a finite set `X` of integers satisfies
`#(X + X) ≤ κ * #X`, where `2 ≤ κ`, and has at least `7 * 10 ^ 7 * κ ^ 2` elements, then
`X + X - (X + X)` contains a proper generalized arithmetic progression `Q` of dimension at most
`3 * 10 ^ 5 * κ ^ 2` with `#X ≤ Real.exp (2 * 10 ^ 7 * κ ^ 2) * #Q.carrier`. -/
theorem exists_proper_gap_subset_add_sub_add_dim_le_card_le' {κ : ℝ} (X : Finset ℤ) (hκ : 2 ≤ κ)
    (hXX : #(X + X) ≤ κ * #X) (hXlower : 7 * 10 ^ 7 * κ ^ 2 ≤ #X) :
    ∃ Q : GAP ℤ, Q.Proper ∧ Q.carrier ⊆ X + X - (X + X) ∧ Q.dim ≤ 3 * 10 ^ 5 * κ ^ 2 ∧
      #X ≤ Real.exp (2 * 10 ^ 7 * κ ^ 2) * #Q.carrier :=
  exists_proper_gap_subset_add_sub_add_dim_le_card_le X hκ hXX hXlower

/-- **Bogolyubov–Ruzsa lemma** in `ZMod q` for a prime `q`. If a set `X` satisfies
`#(X + X) ≤ κ * #X`, where `2 ≤ κ`, and has at least `7 * 10 ^ 7 * κ ^ 2` elements, then
`X + X - (X + X)` contains a proper generalized arithmetic progression `Q` of dimension at most
`3 * 10 ^ 5 * κ ^ 2` with `#X ≤ Real.exp (2 * 10 ^ 7 * κ ^ 2) * #Q.carrier`. -/
theorem exists_proper_gap_zmod_subset_add_sub_add_dim_le_card_le' {q : ℕ} {κ : ℝ}
    (X : Finset (ZMod q)) (hq : q.Prime) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X)
    (hXlower : 7 * 10 ^ 7 * κ ^ 2 ≤ #X) :
    ∃ Q : GAP (ZMod q), Q.Proper ∧ Q.carrier ⊆ X + X - (X + X) ∧ Q.dim ≤ 3 * 10 ^ 5 * κ ^ 2 ∧
      #X ≤ Real.exp (2 * 10 ^ 7 * κ ^ 2) * #Q.carrier :=
  exists_proper_gap_zmod_subset_add_sub_add_dim_le_card_le X hq hκ hXX hXlower

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

/-- **Chang's theorem** for sets of integers, with the dimension bound of Green and Tao. A finite
set `X` of integers with `#(X + X) ≤ κ * #X`, where `2 ≤ κ`, and with `κ * (2 * κ - 1) ≤ ε * #X`
is contained in a `2`-proper generalized arithmetic progression of dimension at most
`⌊κ - 1 + ε⌋₊` with at most `Real.exp (10 ^ 32 * κ ^ 7) * #X` points. -/
theorem exists_twoProperGAP_subset_dim_le_floor_card_le' {κ ε : ℝ} (X : Finset ℤ) (hκ : 2 ≤ κ)
    (hXX : #(X + X) ≤ κ * #X) (hXε : κ * (2 * κ - 1) ≤ ε * #X) :
    ∃ P : GAP ℤ, (P + P).Proper ∧ X ⊆ P.carrier ∧ P.dim ≤ ⌊κ - 1 + ε⌋₊ ∧
      #P.carrier ≤ Real.exp (10 ^ 32 * κ ^ 7) * #X :=
  exists_twoProperGAP_subset_dim_le_floor_card_le X hκ hXX hXε

/-- **Chang's theorem** in `ZMod q` for a prime `q`, with the dimension bound of Green and Tao. A
set `X` with `#(X + X) ≤ κ * #X`, where `2 ≤ κ`, with at least `7 * 10 ^ 7 * κ ^ 2` elements, with
`Real.exp (10 ^ 30 * κ ^ 7) * #X ≤ q` and with `κ * (2 * κ - 1) ≤ ε * #X` is contained in a
`2`-proper generalized arithmetic progression of dimension at most `⌊κ - 1 + ε⌋₊` with at most
`Real.exp (10 ^ 30 * κ ^ 7) * #X` points. -/
theorem exists_twoProperGAP_zmod_subset_dim_le_floor_card_le' {q : ℕ} {κ ε : ℝ}
    (X : Finset (ZMod q)) (hq : q.Prime) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X)
    (hXlower : 7 * 10 ^ 7 * κ ^ 2 ≤ #X) (hXupper : Real.exp (10 ^ 30 * κ ^ 7) * #X ≤ q)
    (hXε : κ * (2 * κ - 1) ≤ ε * #X) :
    ∃ Q : GAP (ZMod q), (Q + Q).Proper ∧ X ⊆ Q.carrier ∧ Q.dim ≤ ⌊κ - 1 + ε⌋₊ ∧
      #Q.carrier ≤ Real.exp (10 ^ 30 * κ ^ 7) * #X :=
  exists_twoProperGAP_zmod_subset_dim_le_floor_card_le X hq hκ hXX hXlower hXupper hXε

end ChangFreimanRuzsa
