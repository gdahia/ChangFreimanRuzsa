/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.Integers
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Polynomial bounds for the budgets of Chang's theorem

For $\kappa \ge 2$, the budgets of `ChangFreimanRuzsa.Cyclic` and `ChangFreimanRuzsa.Integers`
satisfy the following bounds.

* `changContainerExponent κ` is at most $7 \cdot 10^{12} \kappa^5$.
* `changContainerExponent (2 * κ)` is at most $3 \cdot 10^{14} \kappa^5$.
* `changZModExponent κ` is at most $10^{53} \kappa^{20}$.
* `changIntExponent κ` is at least $\kappa^2$ and at most $10^{59} \kappa^{20}$.
-/

public section

namespace ChangFreimanRuzsa

variable {κ : ℝ}

/-! ## The lower bound -/

private lemma four_mul_le_changContainerExponent (hκ : 0 ≤ κ) :
    4 * κ ≤ changContainerExponent κ := by
  have h := changPackBound_nonneg hκ
  unfold changContainerExponent
  linarith [changCoverBound_nonneg hκ, (by positivity : (0 : ℝ) ≤ changGapDim κ),
    (by positivity : 0 ≤ 3 * (changBatchSize κ : ℝ) * changPackBound κ)]

/-- `changIntExponent κ` is at least $\kappa^2$. -/
lemma sq_le_changIntExponent {κ : ℝ} (hκ : 2 ≤ κ) : κ ^ 2 ≤ changIntExponent κ := by
  have h := four_mul_le_changContainerExponent (by linarith : 0 ≤ 2 * κ)
  unfold changIntExponent changZModExponent properizationConstant
  linarith [sq_nonneg κ,
    (pow_le_pow_left₀ (by linarith) (by linarith) 2 :
      κ ^ 2 ≤ (changContainerExponent (2 * κ) + 2) ^ 2),
    (pow_le_pow_right₀ (by linarith) (by norm_num) :
      (changContainerExponent (2 * κ) + 2) ^ 2 ≤ (changContainerExponent (2 * κ) + 2) ^ 4)]

/-! ## The upper bound -/

private lemma changConst_pos : 0 < changConst := by
  unfold changConst
  positivity

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
  have h : (1 : ℝ) ≤ 8 * κ ^ 16 :=
    one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ (by linarith))
  linarith [log_eight_mul_pow_le hκ,
    Nat.ceil_lt_add_one (add_nonneg zero_le_one (Real.log_nonneg h))]

private lemma changDeltaBound_le (hκ : 2 ≤ κ) : (changDeltaBound κ : ℝ) ≤ 250000 * κ ^ 2 := by
  have hκ₀ : 0 ≤ κ := by linarith
  have hc := changConst_pos
  have h : changConst * Real.exp 1 * (⌈1 + Real.log (8 * κ ^ 16)⌉₊ : ℝ) * (8 * (8 * κ)) ≤
      237 * (16 * κ) * (8 * (8 * κ)) := by
    gcongr
    exacts [changConst_mul_exp_one_le, ceil_one_add_log_le hκ]
  unfold changDeltaBound
  nlinarith [Nat.ceil_lt_add_one (R := ℝ) (a := changConst * Real.exp 1 *
    (⌈1 + Real.log (8 * κ ^ 16)⌉₊ : ℝ) * (8 * (8 * κ))) (by positivity)]

private lemma changGapDim_le (hκ : 2 ≤ κ) : (changGapDim κ : ℝ) ≤ 260000 * κ ^ 2 := by
  unfold changGapDim
  push_cast
  nlinarith [changDeltaBound_le hκ]

private lemma changBatchSize_le (hκ : 2 ≤ κ) : (changBatchSize κ : ℝ) ≤ 3.5 * κ := by
  unfold changBatchSize
  linarith [Nat.ceil_lt_add_one (R := ℝ) (a := 3 * κ) (by linarith)]

private lemma changPackBound_le (hκ : 2 ≤ κ) : changPackBound κ ≤ 6.2e11 * κ ^ 4 := by
  have hκ₁ : 1 ≤ κ := by linarith
  unfold changPackBound
  nlinarith [pow_le_pow_left₀ (Nat.cast_nonneg _) (changGapDim_le hκ) 2,
    one_le_pow₀ (n := 4) hκ₁, le_self_pow₀ hκ₁ (by norm_num : 4 ≠ 0)]

private lemma changCoverBound_le (hκ : 2 ≤ κ) : changCoverBound κ ≤ 98 * κ ^ 3 := by
  unfold changCoverBound
  nlinarith [pow_le_pow_left₀ (Nat.cast_nonneg _) (changBatchSize_le hκ) 2]

private lemma batchSize_mul_packBound_le (hκ : 2 ≤ κ) :
    (changBatchSize κ : ℝ) * changPackBound κ ≤ 2.17e12 * κ ^ 5 := by
  linarith [mul_le_mul (changBatchSize_le hκ) (changPackBound_le hκ)
    (changPackBound_nonneg (by linarith)) (by linarith)]

/-- `changContainerExponent κ` is at most $7 \cdot 10^{12} \kappa^5$. -/
lemma changContainerExponent_le (hκ : 2 ≤ κ) :
    changContainerExponent κ ≤ 7 * 10 ^ 12 * κ ^ 5 := by
  have hκ₁ : 1 ≤ κ := by linarith
  unfold changContainerExponent
  linarith [one_le_pow₀ (n := 5) hκ₁, le_self_pow₀ hκ₁ (by norm_num : 5 ≠ 0),
    pow_le_pow_right₀ hκ₁ (by norm_num : 2 ≤ 5), pow_le_pow_right₀ hκ₁ (by norm_num : 3 ≤ 5),
    changGapDim_le hκ, changCoverBound_le hκ, batchSize_mul_packBound_le hκ]

/-- `(changContainerExponent κ + 2) ^ 4` is at most $(7.1 \cdot 10^{12})^4 \kappa^{20}$. -/
lemma changContainerExponent_add_two_pow_le (hκ : 2 ≤ κ) :
    (changContainerExponent κ + 2) ^ 4 ≤ 7.1e12 ^ 4 * κ ^ 20 := by
  rw [(by ring : 7.1e12 ^ 4 * κ ^ 20 = (7.1e12 * κ ^ 5) ^ 4)]
  apply pow_le_pow_left₀
  · linarith [four_mul_le_changContainerExponent (by linarith : 0 ≤ κ)]
  · linarith [changContainerExponent_le hκ, one_le_pow₀ (n := 5) (by linarith : 1 ≤ κ)]

/-- `changZModExponent κ` is at most $10^{53} \kappa^{20}$. -/
lemma changZModExponent_le (hκ : 2 ≤ κ) : changZModExponent κ ≤ 10 ^ 53 * κ ^ 20 := by
  unfold changZModExponent properizationConstant
  linarith [changContainerExponent_le hκ, changContainerExponent_add_two_pow_le hκ,
    pow_le_pow_right₀ (one_le_two.trans hκ) (by norm_num : 5 ≤ 20),
    pow_pos (zero_lt_two.trans_le hκ) 20]

/-- `changIntExponent κ` is at most $10^{59} \kappa^{20}$. -/
lemma changIntExponent_le {κ : ℝ} (hκ : 2 ≤ κ) :
    changIntExponent κ ≤ 10 ^ 59 * κ ^ 20 := by
  have h := changContainerExponent_le (by linarith : 2 ≤ 2 * κ)
  have h' := changContainerExponent_add_two_pow_le (by linarith : 2 ≤ 2 * κ)
  unfold changIntExponent changZModExponent properizationConstant
  rw [mul_pow] at h h'
  norm_num at h h' ⊢
  linarith [pow_le_pow_right₀ (by linarith : 1 ≤ κ) (by norm_num : 5 ≤ 20),
    one_le_pow₀ (n := 20) (by linarith : 1 ≤ κ)]

/-- `changContainerExponent (2 * κ)` is at most $3 \cdot 10^{14} \kappa^5$. This bounds the
dimension in `exists_twoProperGAP_of_small_sumset`. -/
lemma changContainerExponent_two_mul_le (hκ : 2 ≤ κ) :
    changContainerExponent (2 * κ) ≤ 3 * 10 ^ 14 * κ ^ 5 := by
  have h := changContainerExponent_le (κ := 2 * κ) (by linarith)
  rw [mul_pow] at h
  linarith [pow_pos (zero_lt_two.trans_le hκ) 5]

end ChangFreimanRuzsa
