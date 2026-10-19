/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.LatticeBox.GaugeBox
public import Mathlib.Analysis.Complex.Exponential

/-! # Exponential bounds for properization

Each step of the properization of a GAP of dimension $d$ costs a factor $e^{O((d + 2)^3)}$, and the
steps lower the dimension. This file bounds the factors of one step and shows that they telescope
to $e^{O((d + 2)^4)}$.

## Main statements

* `latticeBoxFactor_le_exp_cube`: `latticeBoxFactor k` is at most $e^{(d + 2)^3}$ for $k \le d$.
* `latticeBoxFactor_mul_pow_le_exp_cube` and `pow_mul_two_pow_le_exp_cube`: the factors of one
  step are at most $e^{13 (d + 2)^3}$.
* `mul_pow_four_add_mul_pow_three_le_mul_pow_four`: $A (e + 2)^4 + A (d + 2)^3 \le A (d + 2)^4$
  for $e < d$.
-/

public section

namespace ChangFreimanRuzsa

/-- $2^d \le e^{(d + 2)^3}$. -/
lemma two_pow_le_exp (d : ℕ) : (2 : ℝ) ^ d ≤ Real.exp (((d : ℝ) + 2) ^ 3) := by
  apply (pow_le_pow_left₀ (by norm_num)
    (by linarith [Real.add_one_le_exp (1 : ℝ)] : (2 : ℝ) ≤ Real.exp 1) d).trans
  rw [← Real.exp_nat_mul, mul_one, Real.exp_le_exp]
  nlinarith [Nat.cast_nonneg (α := ℝ) d, sq_nonneg ((d : ℝ) + 2)]

/-- If $0 \le b \le 12 (d + 2)^2$, then $b^d \le e^{12 (d + 2)^3}$. -/
lemma pow_le_exp_cube_of_le_sq {d : ℕ} {b : ℝ} (hb : 0 ≤ b) (hbd : b ≤ 12 * ((d : ℝ) + 2) ^ 2) :
    b ^ d ≤ Real.exp (12 * ((d : ℝ) + 2) ^ 3) := by
  refine (pow_le_pow_left₀ hb (hbd.trans ((Real.add_one_le_exp (12 * ((d : ℝ) + 2) ^ 2)).trans'
    (by linarith))) d).trans ?_
  rw [← Real.exp_nat_mul, Real.exp_le_exp]
  nlinarith [mul_le_mul_of_nonneg_right (by linarith : (d : ℝ) ≤ d + 2)
    (by positivity : 0 ≤ 12 * ((d : ℝ) + 2) ^ 2)]

/-- $4x + 1 \le e^{x + 2}$ for $x \ge 0$. -/
lemma four_mul_add_one_le_exp_add_two {x : ℝ} (hx : 0 ≤ x) : 4 * x + 1 ≤ Real.exp (x + 2) := by
  nlinarith [Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ x + 2), sq_nonneg (x - 1)]

/-- For $k \le d$, `latticeBoxFactor k` is at most $e^{(d + 2)^3}$. -/
lemma latticeBoxFactor_le_exp_cube {k d : ℕ} (hkd : k ≤ d) :
    (latticeBoxFactor k : ℝ) ≤ Real.exp (((d : ℝ) + 2) ^ 3) := by
  refine (Nat.cast_le.mpr (latticeBoxFactor_le_pow k)).trans ?_
  push_cast
  refine (pow_le_pow_left₀ (by positivity)
    (four_mul_add_one_le_exp_add_two k.cast_nonneg) _).trans ?_
  rw [← Real.exp_nat_mul, Real.exp_le_exp]
  push_cast
  nlinarith [pow_le_pow_left₀ (by positivity) (add_le_add_left (Nat.cast_le.mpr hkd) 2 :
      (k : ℝ) + 2 ≤ d + 2) 3,
    sq_nonneg ((k : ℝ) + 2)]

/-- For $r \le d$, the factor `latticeBoxFactor (d - r)` $\cdot ((2r + 4)(2(3r + 1) + 1))^d$ of one
quotient step is at most $e^{13 (d + 2)^3}$. -/
lemma latticeBoxFactor_mul_pow_le_exp_cube {r d : ℕ} (hrd : r ≤ d) :
    (latticeBoxFactor (d - r) : ℝ) * ((2 * (r : ℝ) + 4) * (2 * (3 * (r : ℝ) + 1) + 1)) ^ d ≤
      Real.exp (13 * ((d : ℝ) + 2) ^ 3) := by
  rw [(by ring : 13 * ((d : ℝ) + 2) ^ 3 = ((d : ℝ) + 2) ^ 3 + 12 * ((d : ℝ) + 2) ^ 3),
    Real.exp_add]
  refine mul_le_mul (latticeBoxFactor_le_exp_cube (Nat.sub_le d r))
    (pow_le_exp_cube_of_le_sq (by positivity) ?_) (by positivity) (by positivity)
  nlinarith [pow_le_pow_left₀ (by positivity) (add_le_add_left (Nat.cast_le.mpr hrd) 2 :
    (r : ℝ) + 2 ≤ d + 2) 2]

/-- $(6d + 1)^d \cdot 2^d \le e^{13 (d + 2)^3}$. -/
lemma pow_mul_two_pow_le_exp_cube (d : ℕ) :
    (2 * (3 * (d : ℝ)) + 1) ^ d * (2 : ℝ) ^ d ≤ Real.exp (13 * ((d : ℝ) + 2) ^ 3) := by
  rw [(by ring : 13 * ((d : ℝ) + 2) ^ 3 = 12 * ((d : ℝ) + 2) ^ 3 + ((d : ℝ) + 2) ^ 3),
    Real.exp_add]
  refine mul_le_mul (pow_le_exp_cube_of_le_sq (by positivity) ?_) (two_pow_le_exp d)
    (by positivity) (by positivity)
  nlinarith [Nat.cast_nonneg (α := ℝ) d]

/-- For $A \ge 0$ and $e < d$, $A (e + 2)^4 + A (d + 2)^3 \le A (d + 2)^4$. -/
lemma mul_pow_four_add_mul_pow_three_le_mul_pow_four {A : ℝ} (hA : 0 ≤ A) {e d : ℕ} (hed : e < d) :
    A * ((e : ℝ) + 2) ^ 4 + A * ((d : ℝ) + 2) ^ 3 ≤ A * ((d : ℝ) + 2) ^ 4 := by
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ hA
  nlinarith [pow_le_pow_left₀ (by positivity)
      (by exact_mod_cast Nat.succ_le_succ hed : (e : ℝ) + 2 ≤ d + 1) 4, sq_nonneg ((d : ℝ) + 1),
    mul_nonneg (Nat.cast_nonneg (α := ℝ) d) (sq_nonneg ((d : ℝ) + 1))]

end ChangFreimanRuzsa
