/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.Bound
public import ChangFreimanRuzsa.CoordinateReduction
public import SumOfSetsInSeveralDimensions.FreimanDimensionSumsetBounds

/-!
# Chang's theorem with dimension at most the Freiman dimension

Let `q` be a prime and let `X ⊆ ZMod q` satisfy `|X + X| ≤ κ * |X|`. If `X` is neither too small
nor too large compared with `q`, then `X` lies in a `2`-proper generalized arithmetic progression
of dimension at most `freimanDim X` and of size at most a constant multiple of `|X|`. The same
holds for a finite set of integers that is not too small.

The proof composes three stages: `exists_coarseGAP_container` puts `X` in a progression of bounded
dimension and size, `exists_twoProperGAP_container_of_injOn_nsmul` replaces that progression by a
`2`-proper one, and `exists_twoProperGAP_dim_le_freimanDim_of_injOn_nsmul` replaces the `2`-proper
progression by one of dimension at most `freimanDim X`. For sets of integers the first stage is
`exists_coarseGAP_container_int`.

Since `freimanDim X ≤ 2 * κ - 1` when `|X + X| ≤ κ * |X|`, the progression also has dimension at
most `2 * κ - 1`.

## Main definitions

* `changFreimanDimExponent κ`: the budget for the size of the progression.

## Main statements

* `exists_twoProperGAP_zmod_dim_le_freimanDim`: Chang's theorem in `ZMod q` with dimension at most
  `freimanDim X`.
* `exists_twoProperGAP_int_dim_le_freimanDim`: Chang's theorem for sets of integers with dimension
  at most `freimanDim X`.
* `exists_twoProperGAP_zmod_dim_le_two_mul_sub_one` and
  `exists_twoProperGAP_int_dim_le_two_mul_sub_one`: the same with dimension at most `2 * κ - 1`.
* `changFreimanDimExponent_le`: `changFreimanDimExponent κ ≤ 10 ^ 53 * κ ^ 20` for `κ ≥ 2`.
-/

public section

open Finset SumOfSetsInSeveralDimensions
open scoped Pointwise

namespace ChangFreimanRuzsa

/-- The budget of Chang's theorem in `ZMod q` with the bound for the dimension. -/
@[expose] noncomputable def changFreimanDimExponent (κ : ℝ) : ℝ :=
  (properizationConstant + coordinateReductionConstant) * (changContainerExponent κ + 2) ^ 4 +
    changContainerExponent κ

private lemma exp_mul_le_exp_add_mul {a b c d x y : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hd : 0 ≤ d)
    (hdc : d ≤ c) (hy : 0 ≤ y) (hyx : y ≤ Real.exp c * x) :
    Real.exp (a * (d + 2) ^ 4) * y ≤ Real.exp (b * (c + 2) ^ 4 + c) * x := by
  have hb := ha.trans hab
  rw [Real.exp_add, mul_assoc]
  gcongr

private lemma exp_mul_le_exp_add_mul_add {a b c d e x y z : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (he : 0 ≤ e) (hed : e ≤ d) (hdc : d ≤ c) (hx : 0 ≤ x) (hyx : y ≤ Real.exp c * x)
    (hzy : z ≤ Real.exp (a * (d + 2) ^ 4) * y) :
    Real.exp (b * (e + 2) ^ 4) * z ≤ Real.exp ((a + b) * (c + 2) ^ 4 + c) * x := by
  have hd := he.trans hed
  have hec := hed.trans hdc
  refine (mul_le_mul_of_nonneg_left (hzy.trans (mul_le_mul_of_nonneg_left hyx
    (Real.exp_nonneg _))) (Real.exp_nonneg _)).trans ?_
  rw [add_comm a b, add_mul, Real.exp_add, Real.exp_add, mul_assoc, mul_assoc]
  gcongr

/-- The second and third stages of Chang's theorem, in a group in which the multiples `n • a` with
`n < N` of every nonzero `a` are distinct. Let a nonempty set `X` lie in a progression `P` of
dimension at most `changContainerExponent κ` and of size at most
`exp (changContainerExponent κ) * |X|`. If `exp (changFreimanDimExponent κ) * |X| ≤ N`, then `X`
lies in a `2`-proper progression of dimension at most `freimanDim X` and of size at most
`exp (changFreimanDimExponent κ) * |X|`. -/
theorem exists_twoProperGAP_dim_le_freimanDim_of_coarseGAP {G : Type*} [DecidableEq G]
    [AddCommGroup G] {N : ℕ} {κ : ℝ} {X : Finset G} {P : GAP G}
    (hG : ∀ a : G, a ≠ 0 → Set.InjOn (fun n : ℕ ↦ n • a) (Set.Iio N)) (hX : X.Nonempty)
    (hXP : X ⊆ P.carrier) (hPdim : (P.dim : ℝ) ≤ changContainerExponent κ)
    (hPcard : (#P.carrier : ℝ) ≤ Real.exp (changContainerExponent κ) * #X)
    (hroom : Real.exp (changFreimanDimExponent κ) * #X ≤ N) :
    ∃ Q : GAP G, Q.TwoProper ∧ X ⊆ Q.carrier ∧ (∀ i, 1 < Q.length i) ∧
      Q.dim ≤ freimanDim X ∧ (#Q.carrier : ℝ) ≤ Real.exp (changFreimanDimExponent κ) * #X := by
  have hP : Real.exp (properizationConstant * ((P.dim : ℝ) + 2) ^ 4) * #P.carrier ≤
      Real.exp (changFreimanDimExponent κ) * #X :=
    exp_mul_le_exp_add_mul properizationConstant_pos.le
      (le_add_of_nonneg_right coordinateReductionConstant_pos.le) (Nat.cast_nonneg _) hPdim
      (Nat.cast_nonneg _) hPcard
  obtain ⟨P₂, hP₂, hPP₂, -, hP₂dim, hP₂card⟩ :=
    exists_twoProperGAP_container_of_injOn_nsmul P hG (hP.trans hroom)
  have hP₂room : Real.exp (coordinateReductionConstant * ((P₂.dim : ℝ) + 2) ^ 4) * #P₂.carrier ≤
      Real.exp (changFreimanDimExponent κ) * #X :=
    exp_mul_le_exp_add_mul_add properizationConstant_pos.le coordinateReductionConstant_pos.le
      (Nat.cast_nonneg _) (Nat.cast_le.2 hP₂dim) hPdim (Nat.cast_nonneg _) hPcard hP₂card
  obtain ⟨Q, hQ, hXQ, hlen, hQdim, hQcard⟩ :=
    exists_twoProperGAP_dim_le_freimanDim_of_injOn_nsmul hG hX hP₂ (hXP.trans hPP₂)
      (hP₂room.trans hroom)
  exact ⟨Q, hQ, hXQ, hlen, hQdim, hQcard.trans hP₂room⟩

/-- **Chang's theorem** in `ZMod q` for a prime `q`, with the dimension bounded by the Freiman
dimension: a set `X` with `|X + X| ≤ κ * |X|`, `exp (changContainerExponent κ) < |X|` and
`exp (changFreimanDimExponent κ) * |X| ≤ q` is contained in a `2`-proper GAP of dimension at most
`freimanDim X` and size at most `exp (changFreimanDimExponent κ) * |X|`. -/
theorem exists_twoProperGAP_zmod_dim_le_freimanDim {q : ℕ} {κ : ℝ} (X : Finset (ZMod q))
    (hq : q.Prime) (hκ : 2 ≤ κ) (hXX : (#(X + X) : ℝ) ≤ κ * #X)
    (hXlower : Real.exp (changContainerExponent κ) < #X)
    (hXupper : Real.exp (changFreimanDimExponent κ) * #X ≤ q) :
    ∃ Q : GAP (ZMod q), Q.TwoProper ∧ X ⊆ Q.carrier ∧ (∀ i, 1 < Q.length i) ∧
      Q.dim ≤ freimanDim X ∧ (#Q.carrier : ℝ) ≤ Real.exp (changFreimanDimExponent κ) * #X := by
  obtain ⟨P, hXP, -, hPdim, hPcard⟩ := exists_coarseGAP_container X hq hκ hXX hXlower
  exact exists_twoProperGAP_dim_le_freimanDim_of_coarseGAP
    (fun _ ha ↦ GAP.injOn_nsmul_of_prime hq ha)
    (card_pos.1 (mod_cast (Real.exp_pos _).trans hXlower)) hXP hPdim hPcard hXupper

/-- **Chang's theorem** for sets of integers, with the dimension bounded by the Freiman dimension:
a finite set `X` of integers with `|X + X| ≤ κ * |X|` and `exp (changContainerExponent κ) < |X|`
is contained in a `2`-proper GAP of dimension at most `freimanDim X` and size at most
`exp (changFreimanDimExponent κ) * |X|`. -/
theorem exists_twoProperGAP_int_dim_le_freimanDim {κ : ℝ} (X : Finset ℤ) (hκ : 2 ≤ κ)
    (hXX : (#(X + X) : ℝ) ≤ κ * #X) (hXlower : Real.exp (changContainerExponent κ) < #X) :
    ∃ Q : GAP ℤ, Q.TwoProper ∧ X ⊆ Q.carrier ∧ (∀ i, 1 < Q.length i) ∧
      Q.dim ≤ freimanDim X ∧ (#Q.carrier : ℝ) ≤ Real.exp (changFreimanDimExponent κ) * #X := by
  obtain ⟨P, hXP, -, hPdim, hPcard⟩ := exists_coarseGAP_container_int X hκ hXX hXlower
  exact exists_twoProperGAP_dim_le_freimanDim_of_coarseGAP
    (fun _ ha ↦ GAP.injOn_nsmul_of_isAddTorsionFree _ ha)
    (card_pos.1 (mod_cast (Real.exp_pos _).trans hXlower)) hXP hPdim hPcard (Nat.le_ceil _)

/-- **Chang's theorem** in `ZMod q` for a prime `q`, with dimension at most `2 * κ - 1`: under the
hypotheses of `exists_twoProperGAP_zmod_dim_le_freimanDim`, the Freiman dimension of `X` is at most
`2 * κ - 1`. -/
theorem exists_twoProperGAP_zmod_dim_le_two_mul_sub_one {q : ℕ} {κ : ℝ}
    (X : Finset (ZMod q)) (hq : q.Prime) (hκ : 2 ≤ κ) (hXX : (#(X + X) : ℝ) ≤ κ * #X)
    (hXlower : Real.exp (changContainerExponent κ) < #X)
    (hXupper : Real.exp (changFreimanDimExponent κ) * #X ≤ q) :
    ∃ Q : GAP (ZMod q), Q.TwoProper ∧ X ⊆ Q.carrier ∧ (∀ i, 1 < Q.length i) ∧
      (Q.dim : ℝ) ≤ 2 * κ - 1 ∧ (#Q.carrier : ℝ) ≤ Real.exp (changFreimanDimExponent κ) * #X := by
  obtain ⟨Q, hQ, hXQ, hlen, hQdim, hQcard⟩ :=
    exists_twoProperGAP_zmod_dim_le_freimanDim X hq hκ hXX hXlower hXupper
  exact ⟨Q, hQ, hXQ, hlen, (Nat.cast_le.2 hQdim).trans (freimanDim_le_two_mul_sub_one_of_card_add_le
    (card_pos.1 (mod_cast (Real.exp_pos _).trans hXlower)) hXX), hQcard⟩

/-- **Chang's theorem** for sets of integers, with dimension at most `2 * κ - 1`: under the
hypotheses of `exists_twoProperGAP_int_dim_le_freimanDim`, the Freiman dimension of `X` is at most
`2 * κ - 1`. -/
theorem exists_twoProperGAP_int_dim_le_two_mul_sub_one {κ : ℝ} (X : Finset ℤ) (hκ : 2 ≤ κ)
    (hXX : (#(X + X) : ℝ) ≤ κ * #X) (hXlower : Real.exp (changContainerExponent κ) < #X) :
    ∃ Q : GAP ℤ, Q.TwoProper ∧ X ⊆ Q.carrier ∧ (∀ i, 1 < Q.length i) ∧
      (Q.dim : ℝ) ≤ 2 * κ - 1 ∧ (#Q.carrier : ℝ) ≤ Real.exp (changFreimanDimExponent κ) * #X := by
  obtain ⟨Q, hQ, hXQ, hlen, hQdim, hQcard⟩ :=
    exists_twoProperGAP_int_dim_le_freimanDim X hκ hXX hXlower
  exact ⟨Q, hQ, hXQ, hlen, (Nat.cast_le.2 hQdim).trans (freimanDim_le_two_mul_sub_one_of_card_add_le
    (card_pos.1 (mod_cast (Real.exp_pos _).trans hXlower)) hXX), hQcard⟩

/-- `changFreimanDimExponent κ ≤ 10 ^ 53 * κ ^ 20` for `κ ≥ 2`. -/
lemma changFreimanDimExponent_le {κ : ℝ} (hκ : 2 ≤ κ) :
    changFreimanDimExponent κ ≤ 10 ^ 53 * κ ^ 20 := by
  unfold changFreimanDimExponent coordinateReductionConstant properizationConstant
  linarith [changContainerExponent_le hκ, changContainerExponent_add_two_pow_le hκ,
    pow_le_pow_right₀ (one_le_two.trans hκ) (by norm_num : 5 ≤ 20),
    pow_pos (zero_lt_two.trans_le hκ) 20]

end ChangFreimanRuzsa
