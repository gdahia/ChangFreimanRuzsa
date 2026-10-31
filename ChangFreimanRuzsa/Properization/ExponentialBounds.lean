/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GeometryOfNumbers.GaugeBox

/-!
# Exponential bounds for properization

Each step of the properization of a GAP of dimension `d` costs a factor
`exp (C * (d + 2) ^ 2 * log (d + 2))` for a constant `C`, and the steps lower the dimension. This
file bounds the factors of one step and shows that they telescope to
`exp (C * (d + 2) ^ 3 * log (d + 2))`. The bounds come from writing each factor as a power of
`d + 2`. Passing from `2`-properness to `t`-properness multiplies the factor of one step by
`(t / 2) ^ d`.

## Main statements

* `latticeBoxFactor_le_add_two_pow`: `latticeBoxFactor k` is at most `(d + 2) ^ (2 * (d + 1) ^ 2)`
  for `k ≤ d`.
* `latticeBoxFactor_mul_pow_le_exp`, `latticeBoxFactor_mul_two_pow_le_exp` and
  `two_mul_two_mul_add_one_pow_le_exp`: the factors of one step are at most
  `exp (2 * (d + 2) ^ 2 * log (d + 2))`.
* `latticeBoxFactor_mul_pow_mul_le_exp` and `two_mul_mul_add_one_pow_le_exp`: the factors of one
  step towards `t`-properness, with the additional term `d * log (t / 2)` in the exponent.
* `mul_pow_three_mul_log_add_le`: for `e < d`,
  `A * (e + 2) ^ 3 * log (e + 2) + A * (d + 2) ^ 2 * log (d + 2) ≤ A * (d + 2) ^ 3 * log (d + 2)`.
-/

public section

namespace ChangFreimanRuzsa

lemma log_add_two_pos {x : ℝ} (hx : 0 ≤ x) : 0 < Real.log (x + 2) :=
  Real.log_pos (by linarith)

/-- For `0 ≤ x`, `2 * (x + 2) ^ 2 * log (x + 2) ≤ (x + 2) ^ 3 * log (x + 2)`. -/
lemma two_mul_add_two_sq_mul_log_le {x : ℝ} (hx : 0 ≤ x) :
    2 * (x + 2) ^ 2 * Real.log (x + 2) ≤ (x + 2) ^ 3 * Real.log (x + 2) := by
  nlinarith [mul_nonneg (mul_nonneg hx (sq_nonneg (x + 2))) (log_add_two_pos hx).le]

/-- The map `x ↦ (x + 2) ^ 3 * log (x + 2)` is monotone on `Set.Ici 0`. -/
lemma add_two_pow_three_mul_log_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (x + 2) ^ 3 * Real.log (x + 2) ≤ (y + 2) ^ 3 * Real.log (y + 2) :=
  mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith) 3)
    (Real.log_le_log (by linarith) (by linarith)) (log_add_two_pos hx).le
    (pow_nonneg (by linarith) 3)

/-- If `n ≤ y`, then `(d + 2) ^ n ≤ exp (y * log (d + 2))`. -/
lemma add_two_pow_le_exp_mul_log {d n : ℕ} {y : ℝ} (hny : (n : ℝ) ≤ y) :
    ((d : ℝ) + 2) ^ n ≤ Real.exp (y * Real.log ((d : ℝ) + 2)) := by
  rw [← Real.log_le_iff_le_exp (by positivity), Real.log_pow]
  exact mul_le_mul_of_nonneg_right hny (log_add_two_pos d.cast_nonneg).le

/-- For `k ≤ d`, `latticeBoxFactor k` is at most `(d + 2) ^ (2 * (d + 1) ^ 2)`. -/
lemma latticeBoxFactor_le_add_two_pow {k d : ℕ} (hkd : k ≤ d) :
    latticeBoxFactor k ≤ (d + 2) ^ (2 * (d + 1) ^ 2) := by
  rw [pow_mul (d + 2)]
  exact (latticeBoxFactor_le_pow k).trans
    ((Nat.pow_le_pow_left (by nlinarith : 4 * k + 1 ≤ (d + 2) ^ 2) _).trans
      (Nat.pow_le_pow_right (by positivity) (by nlinarith : (k + 2) * k ≤ (d + 1) ^ 2)))

/-- For `r ≤ d`, the factor `latticeBoxFactor (d - r) * ((2 * r + 4) * (2 * (2 * r + 1) + 1)) ^ d`
of one quotient step is at most `exp (2 * (d + 2) ^ 2 * log (d + 2))`. -/
lemma latticeBoxFactor_mul_pow_le_exp {r d : ℕ} (hrd : r ≤ d) :
    (latticeBoxFactor (d - r) : ℝ) * ((2 * (r : ℝ) + 4) * (2 * (2 * (r : ℝ) + 1) + 1)) ^ d ≤
      Real.exp (2 * ((d : ℝ) + 2) ^ 2 * Real.log ((d : ℝ) + 2)) := by
  have hr : (r : ℝ) ≤ d := Nat.cast_le.mpr hrd
  calc (latticeBoxFactor (d - r) : ℝ) * ((2 * (r : ℝ) + 4) * (2 * (2 * (r : ℝ) + 1) + 1)) ^ d
      ≤ ((d : ℝ) + 2) ^ (2 * (d + 1) ^ 2) * (((d : ℝ) + 2) ^ 4) ^ d := by
        gcongr
        · exact_mod_cast latticeBoxFactor_le_add_two_pow (Nat.sub_le d r)
        · nlinarith [mul_le_mul hr hr (Nat.cast_nonneg r) (Nat.cast_nonneg d),
            pow_nonneg (Nat.cast_nonneg (α := ℝ) d) 3, pow_nonneg (Nat.cast_nonneg (α := ℝ) d) 4,
            Nat.cast_nonneg (α := ℝ) r]
    _ ≤ _ := by
        rw [← pow_mul, ← pow_add]
        exact add_two_pow_le_exp_mul_log (by push_cast; nlinarith)

/-- For `k ≤ d`, `latticeBoxFactor k * 2 ^ d ≤ exp (2 * (d + 2) ^ 2 * log (d + 2))`. -/
lemma latticeBoxFactor_mul_two_pow_le_exp {k d : ℕ} (hkd : k ≤ d) :
    (latticeBoxFactor k : ℝ) * 2 ^ d ≤
      Real.exp (2 * ((d : ℝ) + 2) ^ 2 * Real.log ((d : ℝ) + 2)) := by
  calc (latticeBoxFactor k : ℝ) * 2 ^ d
      ≤ ((d : ℝ) + 2) ^ (2 * (d + 1) ^ 2) * ((d : ℝ) + 2) ^ d := by
        gcongr
        · exact_mod_cast latticeBoxFactor_le_add_two_pow hkd
        · linarith [d.cast_nonneg (α := ℝ)]
    _ ≤ _ := by
        rw [← pow_add]
        exact add_two_pow_le_exp_mul_log (by push_cast; nlinarith)

/-- `(2 * (2 * d) + 1) ^ d ≤ exp ((d + 2) ^ 2 * log (d + 2))`. -/
lemma two_mul_two_mul_add_one_pow_le_exp (d : ℕ) :
    (2 * (2 * (d : ℝ)) + 1) ^ d ≤ Real.exp (((d : ℝ) + 2) ^ 2 * Real.log ((d : ℝ) + 2)) := by
  refine (pow_le_pow_left₀ (by positivity)
    (by nlinarith : 2 * (2 * (d : ℝ)) + 1 ≤ ((d : ℝ) + 2) ^ 2) d).trans ?_
  rw [← pow_mul]
  exact add_two_pow_le_exp_mul_log (by push_cast; nlinarith)

lemma log_div_two_nonneg {t : ℕ} (ht : 2 ≤ t) : 0 ≤ Real.log ((t : ℝ) / 2) :=
  Real.log_nonneg ((one_le_div two_pos).2 (mod_cast ht))

/-- For `2 ≤ t`, `(t / 2) ^ d = exp (d * log (t / 2))`. -/
lemma div_two_pow_eq_exp {t : ℕ} (ht : 2 ≤ t) (d : ℕ) :
    ((t : ℝ) / 2) ^ d = Real.exp (d * Real.log ((t : ℝ) / 2)) := by
  rw [Real.exp_nat_mul, Real.exp_log (div_pos (mod_cast (by grind : 0 < t)) two_pos)]

/-- For `r ≤ d` and `2 ≤ t`, the factor
`latticeBoxFactor (d - r) * ((2 * r + 4) * (2 * (t * r + 1) + 1)) ^ d` of one quotient step is at
most `exp (2 * (d + 2) ^ 2 * log (d + 2) + d * log (t / 2))`. Indeed
`2 * (t * r + 1) + 1 ≤ t / 2 * (2 * (2 * r + 1) + 1)`. -/
lemma latticeBoxFactor_mul_pow_mul_le_exp {r d t : ℕ} (hrd : r ≤ d) (ht : 2 ≤ t) :
    (latticeBoxFactor (d - r) : ℝ) * ((2 * (r : ℝ) + 4) * (2 * (t * (r : ℝ) + 1) + 1)) ^ d ≤
      Real.exp (2 * ((d : ℝ) + 2) ^ 2 * Real.log ((d : ℝ) + 2) + d * Real.log ((t : ℝ) / 2)) := by
  have ht' : (2 : ℝ) ≤ t := mod_cast ht
  have hr := Nat.cast_nonneg (α := ℝ) r
  rw [Real.exp_add, ← div_two_pow_eq_exp ht]
  calc (latticeBoxFactor (d - r) : ℝ) * ((2 * (r : ℝ) + 4) * (2 * (t * (r : ℝ) + 1) + 1)) ^ d
      ≤ (latticeBoxFactor (d - r) : ℝ) *
          ((t : ℝ) / 2 * ((2 * (r : ℝ) + 4) * (2 * (2 * (r : ℝ) + 1) + 1))) ^ d := by
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ d) (Nat.cast_nonneg _)
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * r + 4) (sub_nonneg.2 ht')]
    _ = (latticeBoxFactor (d - r) : ℝ) *
          ((2 * (r : ℝ) + 4) * (2 * (2 * (r : ℝ) + 1) + 1)) ^ d * ((t : ℝ) / 2) ^ d := by
        rw [mul_pow]
        ring
    _ ≤ _ := by
        gcongr
        exact latticeBoxFactor_mul_pow_le_exp hrd

/-- For `2 ≤ t`,
`(2 * (t * d) + 1) ^ d ≤ exp ((d + 2) ^ 2 * log (d + 2) + d * log (t / 2))`. Indeed
`2 * (t * d) + 1 ≤ t / 2 * (2 * (2 * d) + 1)`. -/
lemma two_mul_mul_add_one_pow_le_exp {t : ℕ} (ht : 2 ≤ t) (d : ℕ) :
    (2 * (t * (d : ℝ)) + 1) ^ d ≤
      Real.exp (((d : ℝ) + 2) ^ 2 * Real.log ((d : ℝ) + 2) + d * Real.log ((t : ℝ) / 2)) := by
  have ht' : (2 : ℝ) ≤ t := mod_cast ht
  rw [Real.exp_add, ← div_two_pow_eq_exp ht, mul_comm _ (((t : ℝ) / 2) ^ d)]
  refine (pow_le_pow_left₀ (by positivity)
    (by nlinarith : 2 * (t * (d : ℝ)) + 1 ≤ (t : ℝ) / 2 * (2 * (2 * d) + 1)) d).trans ?_
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left (two_mul_two_mul_add_one_pow_le_exp d) (by positivity)

/-- For `0 ≤ A` and `e < d`,
`A * (e + 2) ^ 3 * log (e + 2) + A * (d + 2) ^ 2 * log (d + 2) ≤ A * (d + 2) ^ 3 * log (d + 2)`.
Indeed `(e + 2) ^ 3 ≤ (d + 1) ^ 3` and `(d + 1) ^ 3 + (d + 2) ^ 2 ≤ (d + 2) ^ 3`. -/
lemma mul_pow_three_mul_log_add_le {A : ℝ} (hA : 0 ≤ A) {e d : ℕ} (hed : e < d) :
    A * ((e : ℝ) + 2) ^ 3 * Real.log ((e : ℝ) + 2) +
        A * ((d : ℝ) + 2) ^ 2 * Real.log ((d : ℝ) + 2) ≤
      A * ((d : ℝ) + 2) ^ 3 * Real.log ((d : ℝ) + 2) := by
  have hL := (log_add_two_pos (Nat.cast_nonneg (α := ℝ) d)).le
  calc A * ((e : ℝ) + 2) ^ 3 * Real.log ((e : ℝ) + 2) +
        A * ((d : ℝ) + 2) ^ 2 * Real.log ((d : ℝ) + 2)
      ≤ A * ((d : ℝ) + 1) ^ 3 * Real.log ((d : ℝ) + 2) +
        A * ((d : ℝ) + 2) ^ 2 * Real.log ((d : ℝ) + 2) := by
        gcongr A * ?_ ^ 3 * ?_ + _
        · exact (log_add_two_pos (Nat.cast_nonneg (α := ℝ) e)).le
        · exact_mod_cast Nat.succ_le_succ hed
        · exact Real.log_le_log (by positivity) (by linarith [(Nat.cast_lt (α := ℝ)).2 hed])
    _ = A * (((d : ℝ) + 1) ^ 3 + ((d : ℝ) + 2) ^ 2) * Real.log ((d : ℝ) + 2) := by ring
    _ ≤ A * ((d : ℝ) + 2) ^ 3 * Real.log ((d : ℝ) + 2) := by
        gcongr
        nlinarith [Nat.cast_nonneg (α := ℝ) d]

end ChangFreimanRuzsa
