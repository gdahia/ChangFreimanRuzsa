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

For `κ ≥ 2`, the budgets of `Cyclic.lean` and `Integers.lean` satisfy

* `changContainerExponent κ ≤ 7 * 10 ^ 12 * κ ^ 5`,
* `changZModExponent κ ≤ 10 ^ 53 * κ ^ 20`,
* `κ ^ 2 ≤ changIntExponent κ ≤ 10 ^ 59 * κ ^ 20`.
-/

public section

namespace ChangFreimanRuzsa

variable {κ : ℝ}

/-! ## The lower bound -/

private lemma four_mul_le_changContainerExponent (hκ : 0 ≤ κ) :
    4 * κ ≤ changContainerExponent κ := by
  have h₁ := changPackBound_nonneg hκ
  have h₂ := changCoverBound_nonneg hκ
  have h₃ : 0 ≤ 3 * (changBatchSize κ : ℝ) * changPackBound κ := by positivity
  have h₄ : (0 : ℝ) ≤ changGapDim κ := Nat.cast_nonneg _
  unfold changContainerExponent
  linarith

/-- `changIntExponent κ ≥ κ ^ 2`. -/
theorem sq_le_changIntExponent {κ : ℝ} (hκ : 2 ≤ κ) : κ ^ 2 ≤ changIntExponent κ := by
  have h := four_mul_le_changContainerExponent (by linarith : 0 ≤ 2 * κ)
  have h₁ : κ ^ 2 ≤ (changContainerExponent (2 * κ) + 2) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h₂ : (changContainerExponent (2 * κ) + 2) ^ 2 ≤ (changContainerExponent (2 * κ) + 2) ^ 4 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  unfold changIntExponent properizationConstant
  linarith [sq_nonneg κ]

/-! ## The upper bound -/

private lemma changConst_pos : 0 < changConst := by
  unfold changConst
  positivity

private lemma changConst_mul_exp_one_le : changConst * Real.exp 1 ≤ 237 := by
  have h : Real.exp 1 ^ 2 ≤ 2.72 ^ 2 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9]) 2
  unfold changConst
  nlinarith

private lemma log_eight_mul_pow_le (hκ : 2 ≤ κ) : Real.log (8 * κ ^ 16) ≤ 16 * κ - 13 := by
  have hκ₀ : 0 < κ := by linarith
  have h₈ : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have h₂ := Real.log_two_lt_d9
  have h := Real.log_le_sub_one_of_pos hκ₀
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, h₈]
  push_cast
  linarith

private lemma ceil_one_add_log_le (hκ : 2 ≤ κ) :
    (⌈1 + Real.log (8 * κ ^ 16)⌉₊ : ℝ) ≤ 16 * κ := by
  have h₁ : (1 : ℝ) ≤ 8 * κ ^ 16 :=
    one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ (by linarith))
  have h := Nat.ceil_lt_add_one (add_nonneg zero_le_one (Real.log_nonneg h₁))
  linarith [log_eight_mul_pow_le hκ]

private lemma changDeltaBound_le (hκ : 2 ≤ κ) : (changDeltaBound κ : ℝ) ≤ 250000 * κ ^ 2 := by
  have hκ₀ : 0 ≤ κ := by linarith
  have hc := changConst_pos
  have h₁ : changConst * Real.exp 1 * (⌈1 + Real.log (8 * κ ^ 16)⌉₊ : ℝ) * (8 * (8 * κ)) ≤
      237 * (16 * κ) * (8 * (8 * κ)) := by
    gcongr
    · exact changConst_mul_exp_one_le
    · exact ceil_one_add_log_le hκ
  have h := Nat.ceil_lt_add_one (R := ℝ) (a := changConst * Real.exp 1 *
    (⌈1 + Real.log (8 * κ ^ 16)⌉₊ : ℝ) * (8 * (8 * κ))) (by positivity)
  unfold changDeltaBound
  nlinarith

private lemma changGapDim_le (hκ : 2 ≤ κ) : (changGapDim κ : ℝ) ≤ 260000 * κ ^ 2 := by
  have h := changDeltaBound_le hκ
  unfold changGapDim
  push_cast
  nlinarith

private lemma changBatchSize_le (hκ : 2 ≤ κ) : (changBatchSize κ : ℝ) ≤ 3.5 * κ := by
  have h := Nat.ceil_lt_add_one (R := ℝ) (a := 3 * κ) (by linarith)
  unfold changBatchSize
  linarith

private lemma changPackBound_le (hκ : 2 ≤ κ) : changPackBound κ ≤ 6.2e11 * κ ^ 4 := by
  have hκ₁ : 1 ≤ κ := by linarith
  have h : (changGapDim κ : ℝ) ^ 2 ≤ (260000 * κ ^ 2) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (changGapDim_le hκ) 2
  have h₀ : 1 ≤ κ ^ 4 := one_le_pow₀ hκ₁
  have h₁ : κ ≤ κ ^ 4 := le_self_pow₀ hκ₁ (by norm_num)
  unfold changPackBound
  nlinarith

private lemma changCoverBound_le (hκ : 2 ≤ κ) : changCoverBound κ ≤ 98 * κ ^ 3 := by
  have hκ₀ : 0 ≤ κ := by linarith
  have h : (changBatchSize κ : ℝ) ^ 2 ≤ (3.5 * κ) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (changBatchSize_le hκ) 2
  have h' := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 8 * κ)
  unfold changCoverBound
  linarith

private lemma batchSize_mul_packBound_le (hκ : 2 ≤ κ) :
    (changBatchSize κ : ℝ) * changPackBound κ ≤ 2.17e12 * κ ^ 5 := by
  have hκ₀ : 0 ≤ κ := by linarith
  have h : (changBatchSize κ : ℝ) * changPackBound κ ≤ 3.5 * κ * (6.2e11 * κ ^ 4) :=
    mul_le_mul (changBatchSize_le hκ) (changPackBound_le hκ) (changPackBound_nonneg hκ₀)
      (by positivity)
  linarith

/-- `changContainerExponent κ ≤ 7 * 10 ^ 12 * κ ^ 5`. -/
lemma changContainerExponent_le (hκ : 2 ≤ κ) :
    changContainerExponent κ ≤ 7 * 10 ^ 12 * κ ^ 5 := by
  have hκ₁ : 1 ≤ κ := by linarith
  have h₀ : 1 ≤ κ ^ 5 := one_le_pow₀ hκ₁
  have h₁ : κ ≤ κ ^ 5 := le_self_pow₀ hκ₁ (by norm_num)
  have h₂ : κ ^ 2 ≤ κ ^ 5 := pow_le_pow_right₀ hκ₁ (by norm_num)
  have h₃ : κ ^ 3 ≤ κ ^ 5 := pow_le_pow_right₀ hκ₁ (by norm_num)
  have hG := changGapDim_le hκ
  have hC := changCoverBound_le hκ
  have hP := batchSize_mul_packBound_le hκ
  unfold changContainerExponent
  linarith

private lemma changContainerExponent_add_two_pow_le (hκ : 2 ≤ κ) :
    (changContainerExponent κ + 2) ^ 4 ≤ 7.1e12 ^ 4 * κ ^ 20 := by
  have hκ₀ : 0 ≤ κ := by linarith
  have h₀ : 1 ≤ κ ^ 5 := one_le_pow₀ (by linarith)
  have h := four_mul_le_changContainerExponent hκ₀
  have h' := changContainerExponent_le hκ
  calc (changContainerExponent κ + 2) ^ 4 ≤ (7.1e12 * κ ^ 5) ^ 4 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 4
    _ = 7.1e12 ^ 4 * κ ^ 20 := by ring

/-- `changZModExponent κ ≤ 10 ^ 53 * κ ^ 20`. -/
lemma changZModExponent_le (hκ : 2 ≤ κ) : changZModExponent κ ≤ 10 ^ 53 * κ ^ 20 := by
  unfold changZModExponent properizationConstant
  linarith [changContainerExponent_le hκ, changContainerExponent_add_two_pow_le hκ,
    pow_le_pow_right₀ (one_le_two.trans hκ) (by norm_num : 5 ≤ 20),
    pow_pos (zero_lt_two.trans_le hκ) 20]

/-- `changIntExponent κ ≤ 10 ^ 59 * κ ^ 20`. -/
theorem changIntExponent_le {κ : ℝ} (hκ : 2 ≤ κ) :
    changIntExponent κ ≤ 10 ^ 59 * κ ^ 20 := by
  have hκ₂ : 2 ≤ 2 * κ := by linarith
  have h := changContainerExponent_le hκ₂
  have h' := changContainerExponent_add_two_pow_le hκ₂
  have h₅ : κ ^ 5 ≤ κ ^ 20 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h₁ : 1 ≤ κ ^ 20 := one_le_pow₀ (by linarith)
  unfold changIntExponent properizationConstant
  rw [mul_pow] at h h'
  norm_num at h h' ⊢
  linarith

end ChangFreimanRuzsa
