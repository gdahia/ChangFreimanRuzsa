/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.Int
public import ChangFreimanRuzsa.ZMod
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Explicit bounds for the exponents in Chang's theorem

For `2 ≤ κ`, the exponents defined in `ChangFreimanRuzsa.Covering.Container`,
`ChangFreimanRuzsa.Properization.ProperProgression`, `ChangFreimanRuzsa.ZMod` and
`ChangFreimanRuzsa.Int` satisfy the following bounds.

* `containerExponent κ` is at most `13 * 10 ^ 7 * κ ^ 2 * (1 + log κ) ^ 2`, hence at most
  `2 * 10 ^ 8 * κ ^ 3`, and `log (containerExponent κ + 2) ≤ 19 * (1 + log κ)`.
* `256 * bohrGAPDim κ` is at most `7 * 10 ^ 7 * κ ^ 2`.
* `8 * bohrLoss (bohrGAPDim κ)` is at most `exp (2 * 10 ^ 7 * κ ^ 2)`.
* `freimanDimExponent κ` is at most `8 * 10 ^ 9 * κ ^ 2 * (1 + log κ) ^ 3`.
* `intFreimanDimExponent κ` is at most `16 * 10 ^ 10 * κ ^ 2 * (1 + log κ) ^ 3`.
* `tProperExponent t R` is at most `2 * κ * log t + 20 * κ ^ 2 * (1 + log κ)` for `R + 1 ≤ 2 * κ`.

The bound `(1 + log κ) ^ 2 ≤ 3 / 2 * κ` comes from `(1 + log κ) ^ n ≤ n ^ n * exp (1 - n) * κ`.
-/

public section

namespace ChangFreimanRuzsa

variable {κ : ℝ}

/-! ## Powers of the logarithm -/

/-- For `1 ≤ κ` and `1 ≤ n`, `(1 + log κ) ^ n ≤ n ^ n * exp (1 - n) * κ`. -/
lemma one_add_log_pow_le (hκ : 1 ≤ κ) {n : ℕ} (hn : 1 ≤ n) :
    (1 + Real.log κ) ^ n ≤ n ^ n * Real.exp (1 - n) * κ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h : (1 + Real.log κ) / n ≤ Real.exp ((1 + Real.log κ) / n - 1) := by
    linarith [Real.add_one_le_exp ((1 + Real.log κ) / n - 1)]
  have hpow := pow_le_pow_left₀ (div_nonneg (by linarith [Real.log_nonneg hκ]) hn'.le) h n
  rw [← Real.exp_nat_mul, div_pow, div_le_iff₀ (by positivity)] at hpow
  refine hpow.trans_eq ?_
  rw [(by field_simp; ring : (n : ℝ) * ((1 + Real.log κ) / n - 1) = (1 - n) + Real.log κ),
    Real.exp_add, Real.exp_log (by linarith)]
  ring

/-- `(1 + log κ) ^ 2 ≤ 3 / 2 * κ` for `1 ≤ κ`. -/
lemma one_add_log_sq_le (hκ : 1 ≤ κ) : (1 + Real.log κ) ^ 2 ≤ 3 / 2 * κ := by
  have h := one_add_log_pow_le hκ one_le_two
  norm_num at h
  nlinarith [Real.exp_neg_one_lt_d9]

/-! ## The lower bound -/

/-- `containerExponent κ` is at least `κ ^ 2`. -/
lemma sq_le_containerExponent (hκ : 0 ≤ κ) : κ ^ 2 ≤ containerExponent κ := by
  have ht : 3 * κ ≤ translateCount κ := Nat.le_ceil _
  have hI : 4 * κ ≤ iterationBound κ := by
    unfold iterationBound
    linarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (bohrGAPDim κ))
      (log_eight_mul_bohrGAPDim_nonneg κ)]
  unfold containerExponent
  nlinarith [mul_le_mul ht (add_le_add_right hI 1) (by linarith) (by positivity),
    Nat.cast_nonneg (α := ℝ) (bohrGAPDim κ)]

/-! ## The upper bounds -/

private lemma changConst_mul_exp_one_le : changConst * Real.exp 1 ≤ 237 := by
  unfold changConst
  nlinarith [(pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9]) 2 :
    Real.exp 1 ^ 2 ≤ 2.72 ^ 2)]

/-- `deltaBound κ` is at most `250000 * κ * (1 + log κ)`. -/
lemma deltaBound_le (hκ : 2 ≤ κ) : deltaBound κ ≤ 250000 * κ * (1 + Real.log κ) := by
  have hL : Real.log (8 * κ ^ 16) ≤ 3 + 16 * Real.log κ := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
      (by norm_num : (8 : ℝ) = 2 ^ 3), Real.log_pow]
    push_cast
    linarith [Real.log_two_lt_d9]
  have hceil : (⌈1 + Real.log (8 * κ ^ 16)⌉₊ : ℝ) ≤ 16 * (1 + Real.log κ) := by
    linarith [Nat.ceil_lt_add_one (add_nonneg zero_le_one (Real.log_nonneg
      (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ (by linarith)) :
        (1 : ℝ) ≤ 8 * κ ^ 16))), Real.log_nonneg (by linarith : (1 : ℝ) ≤ κ)]
  have h : changConst * Real.exp 1 * (⌈1 + Real.log (8 * κ ^ 16)⌉₊ : ℝ) * (8 * (8 * κ)) ≤
      237 * (16 * (1 + Real.log κ)) * (8 * (8 * κ)) := by
    gcongr
    exact changConst_mul_exp_one_le
  unfold deltaBound
  nlinarith [Nat.ceil_lt_add_one (R := ℝ) (a := changConst * Real.exp 1 *
    (⌈1 + Real.log (8 * κ ^ 16)⌉₊ : ℝ) * (8 * (8 * κ))) (by positivity),
    Real.log_nonneg (by linarith : (1 : ℝ) ≤ κ)]

private lemma bohrGAPDim_le (hκ : 2 ≤ κ) : bohrGAPDim κ ≤ 260000 * κ * (1 + Real.log κ) := by
  unfold bohrGAPDim
  push_cast
  nlinarith [deltaBound_le hκ, Real.log_nonneg (by linarith : (1 : ℝ) ≤ κ)]

/-- `256 * bohrGAPDim κ ≤ 7 * 10 ^ 7 * κ ^ 2`. This bounds the size that `#X` has to reach in
Chang's theorem in `ZMod q`. -/
lemma mul_bohrGAPDim_le (hκ : 2 ≤ κ) : 256 * (bohrGAPDim κ : ℝ) ≤ 7 * 10 ^ 7 * κ ^ 2 := by
  nlinarith [bohrGAPDim_le hκ, Real.log_le_sub_one_of_pos (by linarith : 0 < κ)]

private lemma log_eight_mul_bohrGAPDim_le (hκ : 2 ≤ κ) :
    Real.log (8 * bohrGAPDim κ) ≤ 15 * (1 + Real.log κ) := by
  have hL := Real.log_nonneg (by linarith : (1 : ℝ) ≤ κ)
  have hd : (8 : ℝ) * bohrGAPDim κ ≤ 2 ^ 21 * (κ * (1 + Real.log κ)) := by
    nlinarith [bohrGAPDim_le hκ]
  refine (Real.log_le_log (by unfold bohrGAPDim; positivity) hd).trans ?_
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow]
  push_cast
  linarith [Real.log_two_lt_d9, Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + Real.log κ)]

/-- `8 * bohrLoss d ≤ exp (2 * 10 ^ 7 * κ ^ 2)`, where `d` is `bohrGAPDim κ`. This bounds the loss
in the Bogolyubov–Ruzsa lemma. -/
lemma mul_bohrLoss_bohrGAPDim_le (hκ : 2 ≤ κ) :
    8 * bohrLoss (bohrGAPDim κ) ≤ Real.exp (2 * 10 ^ 7 * κ ^ 2) := by
  have hloss := bohrLoss_pos (one_le_bohrGAPDim κ)
  rw [← Real.exp_log (by positivity : 0 < 8 * bohrLoss (bohrGAPDim κ)), Real.exp_le_exp,
    Real.log_mul (by norm_num) hloss.ne', log_bohrLoss]
  nlinarith [mul_le_mul (bohrGAPDim_le hκ) (log_eight_mul_bohrGAPDim_le hκ)
    (log_eight_mul_bohrGAPDim_nonneg κ) ((Nat.cast_nonneg _).trans (bohrGAPDim_le hκ)),
    mul_le_mul_of_nonneg_left (one_add_log_sq_le (by linarith : (1 : ℝ) ≤ κ))
      (by linarith : (0 : ℝ) ≤ κ), Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)]

private lemma translateCount_le (hκ : 2 ≤ κ) : translateCount κ ≤ 7 / 2 * κ := by
  unfold translateCount
  linarith [Nat.ceil_lt_add_one (R := ℝ) (a := 3 * κ) (by linarith)]

private lemma iterationBound_le (hκ : 2 ≤ κ) :
    iterationBound κ ≤ 12 * 10 ^ 6 * κ * (1 + Real.log κ) ^ 2 := by
  have hL := Real.log_nonneg (by linarith : (1 : ℝ) ≤ κ)
  have h := mul_le_mul (bohrGAPDim_le hκ) (log_eight_mul_bohrGAPDim_le hκ)
    (log_eight_mul_bohrGAPDim_nonneg κ) (by positivity)
  unfold iterationBound
  nlinarith [mul_le_mul_of_nonneg_left (one_le_pow₀ (n := 2)
    (by linarith : (1 : ℝ) ≤ 1 + Real.log κ)) (by linarith : (0 : ℝ) ≤ κ)]

/-- `containerExponent κ` is at most `13 * 10 ^ 7 * κ ^ 2 * (1 + log κ) ^ 2`. -/
lemma containerExponent_le_log (hκ : 2 ≤ κ) :
    containerExponent κ ≤ 13 * 10 ^ 7 * κ ^ 2 * (1 + Real.log κ) ^ 2 := by
  have hL := Real.log_nonneg (by linarith : (1 : ℝ) ≤ κ)
  have hℓ : (1 : ℝ) ≤ (1 + Real.log κ) ^ 2 := one_le_pow₀ (by linarith)
  have h := mul_le_mul (translateCount_le hκ) (add_le_add_right (iterationBound_le hκ) 1)
    (by linarith [iterationBound_nonneg (by linarith : (0 : ℝ) ≤ κ)]) (by positivity)
  unfold containerExponent
  nlinarith [bohrGAPDim_le hκ, mul_le_mul_of_nonneg_left hℓ (by positivity : (0 : ℝ) ≤ κ ^ 2),
    mul_le_mul_of_nonneg_right (by nlinarith : (1 : ℝ) + Real.log κ ≤ (1 + Real.log κ) ^ 2)
      (by positivity : (0 : ℝ) ≤ κ)]

/-- `containerExponent κ` is at most `2 * 10 ^ 8 * κ ^ 3`. -/
lemma containerExponent_le (hκ : 2 ≤ κ) : containerExponent κ ≤ 2 * 10 ^ 8 * κ ^ 3 := by
  nlinarith [containerExponent_le_log hκ, one_add_log_sq_le (by linarith : (1 : ℝ) ≤ κ),
    pow_pos (by linarith : (0 : ℝ) < κ) 2]

/-- `log (containerExponent κ + 2) ≤ 19 * (1 + log κ)`. -/
private lemma log_containerExponent_add_two_le (hκ : 2 ≤ κ) :
    Real.log (containerExponent κ + 2) ≤ 19 * (1 + Real.log κ) := by
  have hL := Real.log_nonneg (by linarith : (1 : ℝ) ≤ κ)
  have hc := (sq_nonneg κ).trans (sq_le_containerExponent (by linarith))
  have hM : containerExponent κ + 2 ≤ 2 ^ 27 * (κ ^ 2 * (1 + Real.log κ) ^ 2) := by
    nlinarith [containerExponent_le_log hκ,
      one_le_pow₀ (n := 2) (by linarith : (1 : ℝ) ≤ 1 + Real.log κ),
      mul_le_mul_of_nonneg_right (by nlinarith : (4 : ℝ) ≤ κ ^ 2)
        (by positivity : (0 : ℝ) ≤ (1 + Real.log κ) ^ 2)]
  grw [Real.log_le_log (by linarith) hM]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  linarith [Real.log_two_lt_d9, Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + Real.log κ)]

/-- If `log (c + 2) ≤ 19 * ℓ` with `0 ≤ c` and `1 ≤ ℓ`, then `log (8 * (c + 2) ^ 3) ≤ 60 * ℓ`. -/
private lemma log_eight_mul_add_two_pow_le {c ℓ : ℝ} (hc : 0 ≤ c) (hℓ : 1 ≤ ℓ)
    (h : Real.log (c + 2) ≤ 19 * ℓ) : Real.log (8 * (c + 2) ^ 3) ≤ 60 * ℓ := by
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, (by norm_num : (8 : ℝ) = 2 ^ 3),
    Real.log_pow]
  push_cast
  linarith [Real.log_two_lt_d9]

private lemma log_eight_mul_add_two_pow_nonneg {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ Real.log (8 * (c + 2) ^ 3) :=
  Real.log_nonneg (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ (by linarith)))

/-- `κ ^ 2 * (1 + log κ) ^ 2 ≤ κ ^ 2 * (1 + log κ) ^ 3` and `1 ≤ κ ^ 2 * (1 + log κ) ^ 3`. -/
private lemma sq_mul_one_add_log_sq_le (hκ : 2 ≤ κ) :
    κ ^ 2 * (1 + Real.log κ) ^ 2 ≤ κ ^ 2 * (1 + Real.log κ) ^ 3 ∧
      1 ≤ κ ^ 2 * (1 + Real.log κ) ^ 3 := by
  have hL : (1 : ℝ) ≤ 1 + Real.log κ := by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ κ)]
  exact ⟨mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by norm_num)) (by positivity),
    one_le_mul_of_one_le_of_one_le (by nlinarith) (one_le_pow₀ hL)⟩

/-- `freimanDimExponent κ` is at most `8 * 10 ^ 9 * κ ^ 2 * (1 + log κ) ^ 3`. -/
lemma freimanDimExponent_le (hκ : 2 ≤ κ) :
    freimanDimExponent κ ≤ 8 * 10 ^ 9 * κ ^ 2 * (1 + Real.log κ) ^ 3 := by
  have hL := Real.log_nonneg (by linarith : (1 : ℝ) ≤ κ)
  have hc := (sq_nonneg κ).trans (sq_le_containerExponent (by linarith))
  obtain ⟨h₂, h₃⟩ := sq_mul_one_add_log_sq_le hκ
  unfold freimanDimExponent
  nlinarith [mul_le_mul (containerExponent_le_log hκ) (log_eight_mul_add_two_pow_le hc
    (by linarith) (log_containerExponent_add_two_le hκ)) (log_eight_mul_add_two_pow_nonneg hc)
    (by positivity), containerExponent_le_log hκ]

/-- `intFreimanDimExponent κ` is at most `16 * 10 ^ 10 * κ ^ 2 * (1 + log κ) ^ 3`. -/
lemma intFreimanDimExponent_le (hκ : 2 ≤ κ) :
    intFreimanDimExponent κ ≤ 16 * 10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 := by
  have hL := Real.log_nonneg (by linarith : (1 : ℝ) ≤ κ)
  have hκ' : (2 : ℝ) ≤ 2 * κ := by linarith
  have hc := (sq_nonneg (2 * κ)).trans (sq_le_containerExponent (by linarith))
  have h₁ : 1 + Real.log (2 * κ) ≤ 1.7 * (1 + Real.log κ) := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    linarith [Real.log_two_lt_d9]
  have hcl : containerExponent (2 * κ) ≤ 151 * 10 ^ 7 * κ ^ 2 * (1 + Real.log κ) ^ 2 := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * κ)
    grw [containerExponent_le_log hκ', h₁]
    nlinarith [(by positivity : (0 : ℝ) ≤ κ ^ 2 * (1 + Real.log κ) ^ 2)]
  obtain ⟨h₂, h₃⟩ := sq_mul_one_add_log_sq_le hκ
  unfold intFreimanDimExponent
  nlinarith [mul_le_mul hcl (log_eight_mul_add_two_pow_le (ℓ := 1.7 * (1 + Real.log κ)) hc
    (by linarith) ((log_containerExponent_add_two_le hκ').trans (by linarith)))
    (log_eight_mul_add_two_pow_nonneg hc) (by positivity)]

/-- `tProperExponent t R ≤ 2 * κ * log t + 20 * κ ^ 2 * (1 + log κ)` for `1 ≤ t`, `2 ≤ κ` and
`R + 1 ≤ 2 * κ`. The factorials are bounded by `R ! ≤ R ^ R ≤ (2 * κ) ^ R`. -/
lemma tProperExponent_le {t R : ℕ} (ht : 1 ≤ t) (hκ : 2 ≤ κ) (hR : (R : ℝ) + 1 ≤ 2 * κ) :
    tProperExponent t R ≤ 2 * κ * Real.log t + 20 * κ ^ 2 * (1 + Real.log κ) := by
  have hL := Real.log_nonneg (by linarith : (1 : ℝ) ≤ κ)
  have hR0 := Nat.cast_nonneg (α := ℝ) R
  have hR2 : (R : ℝ) ≤ 2 * κ := by linarith
  have h2κ : Real.log (2 * κ) ≤ 0.7 + Real.log κ := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    linarith [Real.log_two_lt_d9]
  have h3κ : Real.log (R + 2) ≤ 1.1 + Real.log κ := by
    grw [Real.log_le_log (by positivity) (by linarith : (R : ℝ) + 2 ≤ 3 * κ),
      Real.log_mul (by norm_num) (by linarith)]
    linarith [Real.log_three_lt_d9]
  have hfac : Real.log R.factorial ≤ R * (0.7 + Real.log κ) := by
    grw [← h2κ, ← Real.log_pow]
    refine Real.log_le_log (by positivity) ?_
    calc (R.factorial : ℝ) ≤ (R : ℝ) ^ R := by exact_mod_cast Nat.factorial_le_pow R
      _ ≤ (2 * κ) ^ R := by gcongr
  have hf : (0 : ℝ) < R.factorial := by exact_mod_cast Nat.factorial_pos R
  have hR1 : Real.log (R + 1) ≤ 0.7 + Real.log κ :=
    (Real.log_le_log (by positivity) hR).trans h2κ
  unfold tProperExponent
  push_cast
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow]
  push_cast
  have hc : 0 ≤ 0.7 + Real.log κ := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hR2
      (Real.log_nonneg (Nat.one_le_cast.2 ht) : (0 : ℝ) ≤ Real.log t),
    mul_le_mul_of_nonneg_left hfac hR0, mul_le_mul_of_nonneg_left hR1 hR0,
    mul_le_mul_of_nonneg_left h3κ hR0, mul_le_mul_of_nonneg_right hR2 hc,
    mul_le_mul_of_nonneg_right (mul_le_mul hR2 hR2 hR0 (by linarith)) hc,
    mul_le_mul_of_nonneg_right (by nlinarith : κ ≤ κ ^ 2 / 2) hL,
    mul_le_mul_of_nonneg_right hR2 (by norm_num : (0 : ℝ) ≤ 1.8),
    Real.log_two_lt_d9, Real.log_three_lt_d9]

end ChangFreimanRuzsa
