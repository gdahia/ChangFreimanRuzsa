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

* `containerExponent κ` is at most $1.3 \cdot 10^8 \kappa^2 (1 + \log \kappa)^2$, hence at most
  $2 \cdot 10^8 \kappa^3$.
* `containerExponent (2 * κ)` is at most $1.6 \cdot 10^9 \kappa^3$.
* $(c + 2)^3 \log (c + 2)$, where $c$ is `containerExponent κ`, is at most
  $8.8 \cdot 10^{28} \kappa^7$. This bounds the cost of properization.
* `zmodExponent κ` is at most $3 \cdot 10^{29} \kappa^7$.
* `intExponent κ` is at least $\kappa^2$ and at most $4 \cdot 10^{31} \kappa^7$.

The logarithms are removed by $(1 + \log \kappa)^n \le n^n e^{1 - n} \kappa$.
-/

public section

namespace ChangFreimanRuzsa

variable {κ : ℝ}

/-! ## Powers of the logarithm -/

/-- For $\kappa \ge 1$ and $n \ge 1$, $(1 + \log \kappa)^n \le n^n e^{1 - n} \kappa$. -/
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

/-- $(1 + \log \kappa)^2 \le 3 \kappa / 2$ for $\kappa \ge 1$. -/
lemma one_add_log_sq_le (hκ : 1 ≤ κ) : (1 + Real.log κ) ^ 2 ≤ 3 / 2 * κ := by
  have h := one_add_log_pow_le hκ one_le_two
  norm_num at h
  nlinarith [Real.exp_neg_one_lt_d9]

/-- $(1 + \log \kappa)^7 \le 2050 \kappa$ for $\kappa \ge 1$. -/
lemma one_add_log_pow_seven_le (hκ : 1 ≤ κ) : (1 + Real.log κ) ^ 7 ≤ 2050 * κ := by
  have h := one_add_log_pow_le hκ (n := 7) (by norm_num)
  have he : Real.exp (-6) ≤ 0.002479 := by
    rw [(by rw [← Real.exp_nat_mul]; norm_num : Real.exp (-6) = Real.exp (-1) ^ 6)]
    refine (pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_neg_one_lt_d9.le 6).trans ?_
    norm_num
  norm_num at h
  nlinarith

/-! ## The lower bound -/

/-- `containerExponent κ` is at least $\kappa^2$. -/
lemma sq_le_containerExponent (hκ : 0 ≤ κ) : κ ^ 2 ≤ containerExponent κ := by
  have ht : 3 * κ ≤ translateCount κ := Nat.le_ceil _
  have hI : 4 * κ ≤ iterationBound κ := by
    unfold iterationBound
    linarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (bohrGAPDim κ))
      (log_eight_mul_bohrGAPDim_nonneg κ)]
  unfold containerExponent
  nlinarith [mul_le_mul ht (add_le_add_right hI 1) (by linarith) (by positivity),
    Nat.cast_nonneg (α := ℝ) (bohrGAPDim κ)]

/-- `zmodExponent κ` is nonnegative. -/
lemma zmodExponent_nonneg (hκ : 0 ≤ κ) : 0 ≤ zmodExponent κ := by
  have hc := (sq_nonneg κ).trans (sq_le_containerExponent hκ)
  unfold zmodExponent
  linarith [properizationExponent_nonneg hc]

/-- `intExponent κ` is at least $\kappa^2$. -/
lemma sq_le_intExponent (hκ : 2 ≤ κ) : κ ^ 2 ≤ intExponent κ := by
  unfold intExponent
  nlinarith [sq_le_containerExponent (by linarith : 0 ≤ 2 * κ),
    zmodExponent_nonneg (by linarith : 0 ≤ 2 * κ)]

/-! ## The upper bounds -/

private lemma changConst_mul_exp_one_le : changConst * Real.exp 1 ≤ 237 := by
  unfold changConst
  nlinarith [(pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9]) 2 :
    Real.exp 1 ^ 2 ≤ 2.72 ^ 2)]

/-- `deltaBound κ` is at most $2.5 \cdot 10^5 \kappa (1 + \log \kappa)$. -/
lemma deltaBound_le (hκ : 2 ≤ κ) :
    (deltaBound κ : ℝ) ≤ 250000 * κ * (1 + Real.log κ) := by
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

private lemma bohrGAPDim_le (hκ : 2 ≤ κ) :
    (bohrGAPDim κ : ℝ) ≤ 260000 * κ * (1 + Real.log κ) := by
  unfold bohrGAPDim
  push_cast
  nlinarith [deltaBound_le hκ, Real.log_nonneg (by linarith : (1 : ℝ) ≤ κ)]

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

private lemma translateCount_le (hκ : 2 ≤ κ) : (translateCount κ : ℝ) ≤ 7 / 2 * κ := by
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

/-- `containerExponent κ` is at most $1.3 \cdot 10^8 \kappa^2 (1 + \log \kappa)^2$. -/
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

/-- `containerExponent κ` is at most $2 \cdot 10^8 \kappa^3$. -/
lemma containerExponent_le (hκ : 2 ≤ κ) : containerExponent κ ≤ 2 * 10 ^ 8 * κ ^ 3 := by
  nlinarith [containerExponent_le_log hκ, one_add_log_sq_le (by linarith : (1 : ℝ) ≤ κ),
    pow_pos (by linarith : (0 : ℝ) < κ) 2]

/-- `containerExponent (2 * κ)` is at most $1.6 \cdot 10^9 \kappa^3$. This bounds the dimension in
`exists_twoProperGAP_of_small_sumset`. -/
lemma containerExponent_two_mul_le (hκ : 2 ≤ κ) :
    containerExponent (2 * κ) ≤ 16 * 10 ^ 8 * κ ^ 3 := by
  have h := containerExponent_le (κ := 2 * κ) (by linarith)
  rw [mul_pow] at h
  linarith

/-- Write $c$ for `containerExponent κ`. Then $(c + 2)^3 \log (c + 2) \le 8.8 \cdot 10^{28}
\kappa^7$. -/
lemma containerExponent_add_two_pow_mul_log_le (hκ : 2 ≤ κ) :
    (containerExponent κ + 2) ^ 3 * Real.log (containerExponent κ + 2) ≤ 88 * 10 ^ 27 * κ ^ 7 := by
  have hL := Real.log_nonneg (by linarith : (1 : ℝ) ≤ κ)
  have hc := (sq_nonneg κ).trans (sq_le_containerExponent (by linarith))
  have hκℓ : 4 ≤ κ ^ 2 * (1 + Real.log κ) ^ 2 := by
    nlinarith [one_le_pow₀ (n := 2) (by linarith : (1 : ℝ) ≤ 1 + Real.log κ)]
  have hM : containerExponent κ + 2 ≤ 131 * 10 ^ 6 * (κ ^ 2 * (1 + Real.log κ) ^ 2) := by
    linarith [containerExponent_le_log hκ]
  have hlog : Real.log (containerExponent κ + 2) ≤ 19 * (1 + Real.log κ) := by
    refine (Real.log_le_log (by linarith)
      (hM.trans (by gcongr; norm_num : _ ≤ (2 : ℝ) ^ 27 * (κ ^ 2 * (1 + Real.log κ) ^ 2)))).trans ?_
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    linarith [Real.log_two_lt_d9, Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + Real.log κ)]
  calc (containerExponent κ + 2) ^ 3 * Real.log (containerExponent κ + 2)
      ≤ (131 * 10 ^ 6 * (κ ^ 2 * (1 + Real.log κ) ^ 2)) ^ 3 * (19 * (1 + Real.log κ)) :=
        mul_le_mul (pow_le_pow_left₀ (by linarith) hM 3) hlog (Real.log_nonneg (by linarith))
          (by positivity)
    _ = (131 * 10 ^ 6) ^ 3 * 19 * κ ^ 6 * (1 + Real.log κ) ^ 7 := by ring
    _ ≤ (131 * 10 ^ 6) ^ 3 * 19 * κ ^ 6 * (2050 * κ) := by
        gcongr
        exact one_add_log_pow_seven_le (by linarith)
    _ = (131 * 10 ^ 6) ^ 3 * 19 * 2050 * κ ^ 7 := by ring
    _ ≤ 88 * 10 ^ 27 * κ ^ 7 := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

/-- `zmodExponent κ` is at most $3 \cdot 10^{29} \kappa^7$. -/
lemma zmodExponent_le (hκ : 2 ≤ κ) : zmodExponent κ ≤ 3 * 10 ^ 29 * κ ^ 7 := by
  have h := containerExponent_add_two_pow_mul_log_le hκ
  unfold zmodExponent properizationExponent
  rw [mul_assoc]
  linarith [containerExponent_le hκ, one_le_pow₀ (n := 7) (by linarith : (1 : ℝ) ≤ κ),
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ κ) (by norm_num : 3 ≤ 7)]

/-- `intExponent κ` is at most $4 \cdot 10^{31} \kappa^7$. -/
lemma intExponent_le (hκ : 2 ≤ κ) : intExponent κ ≤ 4 * 10 ^ 31 * κ ^ 7 := by
  have h := zmodExponent_le (κ := 2 * κ) (by linarith)
  rw [mul_pow] at h
  unfold intExponent
  linarith [containerExponent_two_mul_le hκ,
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ κ) (by norm_num : 3 ≤ 7),
    one_le_pow₀ (n := 7) (by linarith : (1 : ℝ) ≤ κ)]

end ChangFreimanRuzsa
