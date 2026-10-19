/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.Integers
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Polynomial bounds for the exponents in Chang's theorem

For $\kappa \ge 2$, the exponents defined in `ChangFreimanRuzsa.Container`,
`ChangFreimanRuzsa.Cyclic` and `ChangFreimanRuzsa.Integers` satisfy the following bounds.

* `containerExponent κ` is at most $7 \cdot 10^{12} \kappa^5$.
* `containerExponent (2 * κ)` is at most $3 \cdot 10^{14} \kappa^5$.
* `zmodExponent κ` is at most $10^{53} \kappa^{20}$.
* `intExponent κ` is at least $\kappa^2$ and at most $10^{59} \kappa^{20}$.
-/

public section

namespace ChangFreimanRuzsa

variable {κ : ℝ}

/-! ## The lower bound -/

private lemma four_mul_le_containerExponent (hκ : 0 ≤ κ) :
    4 * κ ≤ containerExponent κ := by
  unfold containerExponent
  linarith [coverBound_nonneg hκ, (by positivity : (0 : ℝ) ≤ bohrGAPDim κ),
    mul_nonneg (by positivity : 0 ≤ 3 * (translateCount κ : ℝ))
      (iterationBound_nonneg hκ)]

/-- `intExponent κ` is at least $\kappa^2$. -/
lemma sq_le_intExponent (hκ : 2 ≤ κ) : κ ^ 2 ≤ intExponent κ := by
  have h := four_mul_le_containerExponent (by linarith : 0 ≤ 2 * κ)
  unfold intExponent zmodExponent properizationConstant
  linarith [sq_nonneg κ,
    (pow_le_pow_left₀ (by linarith) (by linarith) 2 :
      κ ^ 2 ≤ (containerExponent (2 * κ) + 2) ^ 2),
    (pow_le_pow_right₀ (by linarith) (by norm_num) :
      (containerExponent (2 * κ) + 2) ^ 2 ≤ (containerExponent (2 * κ) + 2) ^ 4)]

/-! ## The upper bound -/

private lemma changConst_mul_exp_one_le : changConst * Real.exp 1 ≤ 237 := by
  unfold changConst
  nlinarith [(pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9]) 2 :
    Real.exp 1 ^ 2 ≤ 2.72 ^ 2)]

private lemma log_eight_mul_pow_le (hκ : 2 ≤ κ) : Real.log (8 * κ ^ 16) ≤ 16 * κ - 13 := by
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
    (by norm_num : (8 : ℝ) = 2 ^ 3), Real.log_pow]
  push_cast
  linarith [Real.log_two_lt_d9, Real.log_le_sub_one_of_pos (by linarith : 0 < κ)]

private lemma ceil_one_add_log_le (hκ : 2 ≤ κ) :
    (⌈1 + Real.log (8 * κ ^ 16)⌉₊ : ℝ) ≤ 16 * κ := by
  linarith [log_eight_mul_pow_le hκ, Nat.ceil_lt_add_one (add_nonneg zero_le_one (Real.log_nonneg
    (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ (by linarith)) :
      (1 : ℝ) ≤ 8 * κ ^ 16)))]

private lemma deltaBound_le (hκ : 2 ≤ κ) : (deltaBound κ : ℝ) ≤ 250000 * κ ^ 2 := by
  have h : changConst * Real.exp 1 * (⌈1 + Real.log (8 * κ ^ 16)⌉₊ : ℝ) * (8 * (8 * κ)) ≤
      237 * (16 * κ) * (8 * (8 * κ)) := by
    gcongr
    exacts [changConst_mul_exp_one_le, ceil_one_add_log_le hκ]
  unfold deltaBound
  nlinarith [Nat.ceil_lt_add_one (R := ℝ) (a := changConst * Real.exp 1 *
    (⌈1 + Real.log (8 * κ ^ 16)⌉₊ : ℝ) * (8 * (8 * κ))) (by positivity)]

private lemma bohrGAPDim_le (hκ : 2 ≤ κ) : (bohrGAPDim κ : ℝ) ≤ 260000 * κ ^ 2 := by
  unfold bohrGAPDim
  push_cast
  nlinarith [deltaBound_le hκ]

private lemma translateCount_le (hκ : 2 ≤ κ) : (translateCount κ : ℝ) ≤ 3.5 * κ := by
  unfold translateCount
  linarith [Nat.ceil_lt_add_one (R := ℝ) (a := 3 * κ) (by linarith)]

private lemma iterationBound_le (hκ : 2 ≤ κ) : iterationBound κ ≤ 6.2e11 * κ ^ 4 := by
  have hκ₁ : 1 ≤ κ := by linarith
  unfold iterationBound
  nlinarith [pow_le_pow_left₀ (Nat.cast_nonneg _) (bohrGAPDim_le hκ) 2,
    one_le_pow₀ (n := 4) hκ₁, le_self_pow₀ hκ₁ (by norm_num : 4 ≠ 0)]

private lemma coverBound_le (hκ : 2 ≤ κ) : coverBound κ ≤ 98 * κ ^ 3 := by
  unfold coverBound
  nlinarith [pow_le_pow_left₀ (Nat.cast_nonneg _) (translateCount_le hκ) 2]

private lemma translateCount_mul_iterationBound_le (hκ : 2 ≤ κ) :
    (translateCount κ : ℝ) * iterationBound κ ≤ 2.17e12 * κ ^ 5 := by
  linarith [mul_le_mul (translateCount_le hκ) (iterationBound_le hκ)
    (iterationBound_nonneg (by linarith)) (by linarith)]

/-- `containerExponent κ` is at most $7 \cdot 10^{12} \kappa^5$. -/
lemma containerExponent_le (hκ : 2 ≤ κ) :
    containerExponent κ ≤ 7 * 10 ^ 12 * κ ^ 5 := by
  have hκ₁ : 1 ≤ κ := by linarith
  unfold containerExponent
  linarith [one_le_pow₀ (n := 5) hκ₁, le_self_pow₀ hκ₁ (by norm_num : 5 ≠ 0),
    pow_le_pow_right₀ hκ₁ (by norm_num : 2 ≤ 5), pow_le_pow_right₀ hκ₁ (by norm_num : 3 ≤ 5),
    bohrGAPDim_le hκ, coverBound_le hκ, translateCount_mul_iterationBound_le hκ]

/-- `(containerExponent κ + 2) ^ 4` is at most $(7.1 \cdot 10^{12})^4 \kappa^{20}$. -/
lemma containerExponent_add_two_pow_le (hκ : 2 ≤ κ) :
    (containerExponent κ + 2) ^ 4 ≤ 7.1e12 ^ 4 * κ ^ 20 := by
  rw [(by ring : 7.1e12 ^ 4 * κ ^ 20 = (7.1e12 * κ ^ 5) ^ 4)]
  apply pow_le_pow_left₀
  · linarith [four_mul_le_containerExponent (by linarith : 0 ≤ κ)]
  · linarith [containerExponent_le hκ, one_le_pow₀ (n := 5) (by linarith : 1 ≤ κ)]

/-- `zmodExponent κ` is at most $10^{53} \kappa^{20}$. -/
lemma zmodExponent_le (hκ : 2 ≤ κ) : zmodExponent κ ≤ 10 ^ 53 * κ ^ 20 := by
  unfold zmodExponent properizationConstant
  linarith [containerExponent_le hκ, containerExponent_add_two_pow_le hκ,
    pow_le_pow_right₀ (one_le_two.trans hκ) (by norm_num : 5 ≤ 20),
    pow_pos (zero_lt_two.trans_le hκ) 20]

/-- `intExponent κ` is at most $10^{59} \kappa^{20}$. -/
lemma intExponent_le (hκ : 2 ≤ κ) :
    intExponent κ ≤ 10 ^ 59 * κ ^ 20 := by
  have h := containerExponent_le (by linarith : 2 ≤ 2 * κ)
  have h' := containerExponent_add_two_pow_le (by linarith : 2 ≤ 2 * κ)
  unfold intExponent zmodExponent properizationConstant
  rw [mul_pow] at h h'
  norm_num at h h' ⊢
  linarith [pow_le_pow_right₀ (by linarith : 1 ≤ κ) (by norm_num : 5 ≤ 20),
    one_le_pow₀ (n := 20) (by linarith : 1 ≤ κ)]

/-- `containerExponent (2 * κ)` is at most $3 \cdot 10^{14} \kappa^5$. This bounds the
dimension in `exists_twoProperGAP_of_small_sumset`. -/
lemma containerExponent_two_mul_le (hκ : 2 ≤ κ) :
    containerExponent (2 * κ) ≤ 3 * 10 ^ 14 * κ ^ 5 := by
  have h := containerExponent_le (κ := 2 * κ) (by linarith)
  rw [mul_pow] at h
  linarith [pow_pos (zero_lt_two.trans_le hκ) 5]

end ChangFreimanRuzsa
