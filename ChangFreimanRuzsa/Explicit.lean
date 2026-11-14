/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GAP.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import SumOfSetsInSeveralDimensions.FreimanDimension
import ChangFreimanRuzsa.ExponentBounds
import SumOfSetsInSeveralDimensions.FreimanDimensionSumsetBounds

/-!
# Chang's theorem with explicit bounds

Chang's theorem for finite sets of integers and for subsets of `ZMod q` with `q` prime, with the
exponents in `exists_tProperGAP_int_dim_le_freimanDim` and
`exists_tProperGAP_zmod_dim_le_freimanDim` replaced by the bounds of
`ChangFreimanRuzsa.ExponentBounds`. For `2 ≤ κ` and `2 ≤ t`, a set `X` with `#(X + X) ≤ κ * #X`
lies in a `t`-proper progression of dimension at most `freimanDim X` with at most
`exp (C * κ ^ 2 * (1 + log κ) ^ 3 + 2 * κ * log t) * #X` points, for an absolute constant `C`. This
is the bound of Chang. The Freiman dimension of `X` is at most `2 * κ - 1`, so the progression has
dimension at most `2 * κ - 1`. It is also at most `κ - 1 + κ * (2 * κ - 1) / #X`, so the
progression has dimension at most `⌊κ - 1 + ε⌋₊` when `κ * (2 * κ - 1) ≤ ε * #X`, as in Green and
Tao.

The file also gives the Bogolyubov–Ruzsa lemma with explicit bounds of the form of Chang's
Proposition 2.1, the first step of the proof: for a nonempty `X`, the set `2 • X - 2 • X` contains a
proper progression of dimension at most `3 * 10 ^ 5 * κ * (1 + log κ)` with at least
`#X / exp (2 * 10 ^ 7 * κ * (1 + log κ) ^ 2)` points.

## Main statements

* `exists_proper_gap_subset_nsmul_sub_nsmul_dim_le_card_le`: the Bogolyubov–Ruzsa lemma for sets of
  integers.
* `exists_proper_gap_zmod_subset_nsmul_sub_nsmul_dim_le_card_le`: the Bogolyubov–Ruzsa lemma in
  `ZMod q`.
* `exists_tProperGAP_subset_dim_le_freimanDim_card_le`: the explicit form for sets of integers,
  with dimension at most `freimanDim X`.
* `exists_tProperGAP_zmod_subset_dim_le_freimanDim_card_le`: the explicit form in `ZMod q`, with
  dimension at most `freimanDim X`.
* `exists_tProperGAP_subset_dim_le_card_le`: the explicit form for sets of integers, with
  dimension at most `2 * κ - 1`.
* `exists_tProperGAP_zmod_subset_dim_le_card_le`: the explicit form in `ZMod q`, with dimension
  at most `2 * κ - 1`.
* `exists_tProperGAP_subset_dim_le_floor_card_le`: the explicit form for sets of integers with
  `κ * (2 * κ - 1) ≤ ε * #X`, with dimension at most `⌊κ - 1 + ε⌋₊`.
* `exists_tProperGAP_zmod_subset_dim_le_floor_card_le`: the explicit form in `ZMod q` with
  `κ * (2 * κ - 1) ≤ ε * #X`, with dimension at most `⌊κ - 1 + ε⌋₊`.
-/

public section

open Finset SumOfSetsInSeveralDimensions
open scoped Pointwise

namespace ChangFreimanRuzsa

/-- The progression `{0}` of dimension `0` is proper and lies in `2 • X - 2 • X` for a nonempty
`X`. -/
private lemma exists_proper_gap_subset_nsmul_sub_nsmul_dim_eq_zero {G : Type*} [AddCommGroup G]
    [DecidableEq G] {X : Finset G} (hX : X.Nonempty) :
    ∃ Q : GAP G, Q.Proper ∧ Q.toFinset ⊆ 2 • X - 2 • X ∧ Q.dim = 0 ∧ #Q.toFinset = 1 := by
  have hQ : (⟨0, 0⟩ : GAP G).toFinset = {0} := by
    ext x
    simp [GAP.mem_toFinset, nonpos_iff_eq_zero, GAP.eval, eq_comm]
  refine ⟨⟨0, 0⟩, ?_, ?_, by simp [GAP.dim], by simp [hQ]⟩
  · intro c hc c' hc' _
    rw [nonpos_iff_eq_zero.1 (Set.mem_Iic.1 hc), nonpos_iff_eq_zero.1 (Set.mem_Iic.1 hc')]
  · rw [hQ, singleton_subset_iff]
    exact hX.nsmul.zero_mem_sub

/-- The Bogolyubov–Ruzsa lemma with the bounds of Chang for a nonempty `X` satisfying the
conclusion of `exists_proper_gap_int_subset_add_sub_add_card_le` whenever
`256 * bohrGAPDim κ ≤ #X`. Smaller sets take the progression `{0}`. -/
private lemma exists_proper_gap_subset_nsmul_sub_nsmul_of_bohr {G : Type*} [AddCommGroup G]
    [DecidableEq G] {κ : ℝ} {X : Finset G} (hX : X.Nonempty) (hκ : 2 ≤ κ)
    (h : 256 * (bohrGAPDim κ : ℝ) ≤ #X → ∃ (X₁ : Finset G) (Q : GAP G), X₁ ⊆ X ∧ #X ≤ 8 * #X₁ ∧
      Q.Proper ∧ (Q.dim : ℝ) ≤ bohrGAPDim κ ∧ Q.toFinset ⊆ X + X - (X + X) ∧
        #X ≤ 8 * bohrLoss (bohrGAPDim κ) * #Q.toFinset) :
    ∃ Q : GAP G, Q.Proper ∧ Q.toFinset ⊆ 2 • X - 2 • X ∧
      Q.dim ≤ 3 * 10 ^ 5 * κ * (1 + Real.log κ) ∧
      #X ≤ Real.exp (2 * 10 ^ 7 * κ * (1 + Real.log κ) ^ 2) * #Q.toFinset := by
  have hL := Real.log_nonneg (by linarith : (1 : ℝ) ≤ κ)
  by_cases hXlower : 256 * (bohrGAPDim κ : ℝ) ≤ #X
  · obtain ⟨-, Q, -, -, hQ, hdim, hsub, hcard⟩ := h hXlower
    refine ⟨Q, hQ, by rwa [two_nsmul], ?_, hcard.trans ?_⟩
    · nlinarith [bohrGAPDim_le hκ]
    · grw [mul_bohrLoss_bohrGAPDim_le hκ]
  · obtain ⟨Q, hQ, hsub, hdim, hcard⟩ := exists_proper_gap_subset_nsmul_sub_nsmul_dim_eq_zero hX
    refine ⟨Q, hQ, hsub, ?_, ?_⟩
    · rw [hdim, Nat.cast_zero]
      positivity
    · rw [hcard, Nat.cast_one, mul_one]
      linarith [thirty_two_mul_le_bohrLoss (one_le_bohrGAPDim κ), mul_bohrLoss_bohrGAPDim_le hκ]

/-- **Bogolyubov–Ruzsa lemma** for sets of integers, with the bounds of Chang. If a finite nonempty
set `X` of integers satisfies `#(X + X) ≤ κ * #X`, where `2 ≤ κ`, then `2 • X - 2 • X` contains a
proper generalized arithmetic progression `Q` of dimension at most
`3 * 10 ^ 5 * κ * (1 + log κ)` with `#X ≤ exp (2 * 10 ^ 7 * κ * (1 + log κ) ^ 2) * #Q.toFinset`. -/
theorem exists_proper_gap_subset_nsmul_sub_nsmul_dim_le_card_le {κ : ℝ} (X : Finset ℤ)
    (hX : X.Nonempty) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X) :
    ∃ Q : GAP ℤ, Q.Proper ∧ Q.toFinset ⊆ 2 • X - 2 • X ∧
      Q.dim ≤ 3 * 10 ^ 5 * κ * (1 + Real.log κ) ∧
      #X ≤ Real.exp (2 * 10 ^ 7 * κ * (1 + Real.log κ) ^ 2) * #Q.toFinset :=
  exists_proper_gap_subset_nsmul_sub_nsmul_of_bohr hX hκ
    (exists_proper_gap_int_subset_add_sub_add_card_le X hκ hXX)

/-- **Bogolyubov–Ruzsa lemma** in `ZMod q` for a prime `q`, with the bounds of Chang. If a nonempty
set `X` satisfies `#(X + X) ≤ κ * #X`, where `2 ≤ κ`, then `2 • X - 2 • X` contains a proper
generalized arithmetic progression `Q` of dimension at most `3 * 10 ^ 5 * κ * (1 + log κ)` with
`#X ≤ exp (2 * 10 ^ 7 * κ * (1 + log κ) ^ 2) * #Q.toFinset`. -/
theorem exists_proper_gap_zmod_subset_nsmul_sub_nsmul_dim_le_card_le {q : ℕ} {κ : ℝ}
    (X : Finset (ZMod q)) (hq : q.Prime) (hX : X.Nonempty) (hκ : 2 ≤ κ)
    (hXX : #(X + X) ≤ κ * #X) :
    ∃ Q : GAP (ZMod q), Q.Proper ∧ Q.toFinset ⊆ 2 • X - 2 • X ∧
      Q.dim ≤ 3 * 10 ^ 5 * κ * (1 + Real.log κ) ∧
      #X ≤ Real.exp (2 * 10 ^ 7 * κ * (1 + Real.log κ) ^ 2) * #Q.toFinset :=
  exists_proper_gap_subset_nsmul_sub_nsmul_of_bohr hX hκ
    (exists_proper_gap_zmod_subset_add_sub_add_card_le X hq hκ hXX)

/-- If `#(X + X) ≤ κ * #X` for a nonempty `X`, where `2 ≤ κ`, and
`E ≤ D * κ ^ 2 * (1 + log κ) ^ 3` with `D + 20 ≤ C`, then
`E + tProperExponent t (freimanDim X) ≤ C * κ ^ 2 * (1 + log κ) ^ 3 + 2 * κ * log t`. Indeed
`freimanDim X + 1 ≤ 2 * κ`, so `tProperExponent_le` applies. -/
private lemma add_tProperExponent_freimanDim_le {G : Type*} [DecidableEq G] [AddCancelCommMonoid G]
    {t : ℕ} {κ C D E : ℝ} {X : Finset G} (hX : X.Nonempty) (ht : 2 ≤ t) (hκ : 2 ≤ κ)
    (hXX : #(X + X) ≤ κ * #X) (hE : E ≤ D * κ ^ 2 * (1 + Real.log κ) ^ 3) (hDC : D + 20 ≤ C) :
    E + tProperExponent t (freimanDim X) ≤
      C * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t := by
  have hL : (1 : ℝ) ≤ 1 + Real.log κ := by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ κ)]
  have hT := tProperExponent_le (R := freimanDim X) (by grind : 1 ≤ t) hκ
    (by linarith [freimanDim_le_two_mul_sub_one_of_card_add_le hX hXX])
  have hK : (0 : ℝ) ≤ κ ^ 2 * (1 + Real.log κ) ^ 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (le_self_pow₀ hL (by norm_num : 3 ≠ 0))
    (by positivity : (0 : ℝ) ≤ κ ^ 2), mul_nonneg (by linarith : 0 ≤ C - D - 20) hK]

/-- **Chang's theorem** for sets of integers, with the dimension bounded by the Freiman dimension.
Let `2 ≤ t`. A finite nonempty set `X` of integers with `#(X + X) ≤ κ * #X`, where `2 ≤ κ`, is
contained in a `t`-proper generalized arithmetic progression of dimension at most `freimanDim X`
with at most `Real.exp (2 * 10 ^ 11 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X`
points. -/
theorem exists_tProperGAP_subset_dim_le_freimanDim_card_le {t : ℕ} {κ : ℝ} (X : Finset ℤ)
    (hX : X.Nonempty) (ht : 2 ≤ t) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X) :
    ∃ P : GAP ℤ, (t • P).Proper ∧ X ⊆ P.toFinset ∧ P.dim ≤ freimanDim X ∧
      #P.toFinset ≤
        Real.exp (2 * 10 ^ 11 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X := by
  obtain ⟨P, hP, hXP, hdim, hcard⟩ := exists_tProperGAP_int_dim_le_freimanDim X hX ht hκ hXX
  refine ⟨P, hP, hXP, hdim, hcard.trans ?_⟩
  grw [add_tProperExponent_freimanDim_le (C := 2 * 10 ^ 11) hX ht hκ hXX
    (intFreimanDimExponent_le hκ) (by norm_num)]

/-- **Chang's theorem** in `ZMod q` for a prime `q`, with the dimension bounded by the Freiman
dimension. Let `2 ≤ t`. A set `X` with `#(X + X) ≤ κ * #X`, where `2 ≤ κ`, with at least
`7 * 10 ^ 7 * κ ^ 2` elements and with
`Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X ≤ q`, is contained in a
`t`-proper generalized arithmetic progression of dimension at most `freimanDim X` with at most
`Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X` points. -/
theorem exists_tProperGAP_zmod_subset_dim_le_freimanDim_card_le {q t : ℕ} {κ : ℝ}
    (X : Finset (ZMod q)) (hq : q.Prime) (ht : 2 ≤ t) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X)
    (hXlower : 7 * 10 ^ 7 * κ ^ 2 ≤ #X)
    (hXupper : Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X ≤ q) :
    ∃ Q : GAP (ZMod q), (t • Q).Proper ∧ X ⊆ Q.toFinset ∧ Q.dim ≤ freimanDim X ∧
      #Q.toFinset ≤
        Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X := by
  have hXd := (mul_bohrGAPDim_le hκ).trans hXlower
  have he : Real.exp (freimanDimExponent κ + tProperExponent t (freimanDim X)) * #X ≤
      Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X := by
    grw [add_tProperExponent_freimanDim_le (C := 10 ^ 10) (nonempty_of_mul_bohrGAPDim_le hXd) ht
      hκ hXX (freimanDimExponent_le hκ) (by norm_num)]
  obtain ⟨Q, hQ, hXQ, hdim, hcard⟩ := exists_tProperGAP_zmod_dim_le_freimanDim X hq ht hκ hXX hXd
    (he.trans hXupper)
  exact ⟨Q, hQ, hXQ, hdim, hcard.trans he⟩

/-- **Chang's theorem** for sets of integers. Let `2 ≤ t`. A finite nonempty set `X` of integers
with `#(X + X) ≤ κ * #X`, where `2 ≤ κ`, is contained in a `t`-proper generalized arithmetic
progression of dimension at most `2 * κ - 1` with at most
`Real.exp (2 * 10 ^ 11 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X` points. The
Freiman dimension of `X` is at most `2 * κ - 1`. -/
theorem exists_tProperGAP_subset_dim_le_card_le {t : ℕ} {κ : ℝ} (X : Finset ℤ) (hX : X.Nonempty)
    (ht : 2 ≤ t) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X) :
    ∃ P : GAP ℤ, (t • P).Proper ∧ X ⊆ P.toFinset ∧ P.dim ≤ 2 * κ - 1 ∧
      #P.toFinset ≤
        Real.exp (2 * 10 ^ 11 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X := by
  obtain ⟨P, hP, hXP, hdim, hcard⟩ :=
    exists_tProperGAP_subset_dim_le_freimanDim_card_le X hX ht hκ hXX
  exact ⟨P, hP, hXP,
    (Nat.cast_le.2 hdim).trans (freimanDim_le_two_mul_sub_one_of_card_add_le hX hXX), hcard⟩

/-- **Chang's theorem** in `ZMod q` for a prime `q`. Let `2 ≤ t`. A set `X` with
`#(X + X) ≤ κ * #X`, where `2 ≤ κ`, with at least `7 * 10 ^ 7 * κ ^ 2` elements and with
`Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X ≤ q`, is contained in a
`t`-proper generalized arithmetic progression of dimension at most `2 * κ - 1` with at most
`Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X` points. The Freiman
dimension of `X` is at most `2 * κ - 1`. -/
theorem exists_tProperGAP_zmod_subset_dim_le_card_le {q t : ℕ} {κ : ℝ} (X : Finset (ZMod q))
    (hq : q.Prime) (ht : 2 ≤ t) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X)
    (hXlower : 7 * 10 ^ 7 * κ ^ 2 ≤ #X)
    (hXupper : Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X ≤ q) :
    ∃ Q : GAP (ZMod q), (t • Q).Proper ∧ X ⊆ Q.toFinset ∧ Q.dim ≤ 2 * κ - 1 ∧
      #Q.toFinset ≤
        Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X := by
  obtain ⟨Q, hQ, hXQ, hdim, hcard⟩ :=
    exists_tProperGAP_zmod_subset_dim_le_freimanDim_card_le X hq ht hκ hXX hXlower hXupper
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

/-- **Chang's theorem** for sets of integers, with the dimension bound of Green and Tao. Let
`2 ≤ t`. A finite set `X` of integers with `#(X + X) ≤ κ * #X`, where `2 ≤ κ`, and with
`κ * (2 * κ - 1) ≤ ε * #X` is contained in a `t`-proper generalized arithmetic progression of
dimension at most `⌊κ - 1 + ε⌋₊` with at most
`Real.exp (2 * 10 ^ 11 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X` points. -/
theorem exists_tProperGAP_subset_dim_le_floor_card_le {t : ℕ} {κ ε : ℝ} (X : Finset ℤ) (ht : 2 ≤ t)
    (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X) (hXε : κ * (2 * κ - 1) ≤ ε * #X) :
    ∃ P : GAP ℤ, (t • P).Proper ∧ X ⊆ P.toFinset ∧ P.dim ≤ ⌊κ - 1 + ε⌋₊ ∧
      #P.toFinset ≤
        Real.exp (2 * 10 ^ 11 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X := by
  obtain rfl | hX := X.eq_empty_or_nonempty
  · simp at hXε
    nlinarith
  obtain ⟨P, hP, hXP, hdim, hcard⟩ :=
    exists_tProperGAP_subset_dim_le_freimanDim_card_le X hX ht hκ hXX
  exact ⟨P, hP, hXP, hdim.trans (freimanDim_le_floor_sub_one_add_of_card_add_le hX hXX hXε),
    hcard⟩

/-- **Chang's theorem** in `ZMod q` for a prime `q`, with the dimension bound of Green and Tao. Let
`2 ≤ t`. A set `X` with `#(X + X) ≤ κ * #X`, where `2 ≤ κ`, with at least `7 * 10 ^ 7 * κ ^ 2`
elements, with `Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X ≤ q`
and with `κ * (2 * κ - 1) ≤ ε * #X` is contained in a `t`-proper generalized arithmetic progression
of dimension at most `⌊κ - 1 + ε⌋₊` with at most
`Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X` points. -/
theorem exists_tProperGAP_zmod_subset_dim_le_floor_card_le {q t : ℕ} {κ ε : ℝ}
    (X : Finset (ZMod q)) (hq : q.Prime) (ht : 2 ≤ t) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X)
    (hXlower : 7 * 10 ^ 7 * κ ^ 2 ≤ #X)
    (hXupper : Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X ≤ q)
    (hXε : κ * (2 * κ - 1) ≤ ε * #X) :
    ∃ Q : GAP (ZMod q), (t • Q).Proper ∧ X ⊆ Q.toFinset ∧ Q.dim ≤ ⌊κ - 1 + ε⌋₊ ∧
      #Q.toFinset ≤
        Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X := by
  obtain ⟨Q, hQ, hXQ, hdim, hcard⟩ :=
    exists_tProperGAP_zmod_subset_dim_le_freimanDim_card_le X hq ht hκ hXX hXlower hXupper
  exact ⟨Q, hQ, hXQ, hdim.trans (freimanDim_le_floor_sub_one_add_of_card_add_le
    (nonempty_of_mul_bohrGAPDim_le ((mul_bohrGAPDim_le hκ).trans hXlower)) hXX hXε), hcard⟩

end ChangFreimanRuzsa
