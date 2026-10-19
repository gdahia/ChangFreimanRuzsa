/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.LatticeBox.GaugeBox
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Exponential bounds for properization

Each step of the properization of a GAP of dimension $d$ costs a factor
$e^{O((d + 2)^2 \log (d + 2))}$, and the steps lower the dimension. This file bounds the factors of
one step and shows that they telescope to $e^{O((d + 2)^3 \log (d + 2))}$. The bounds come from
writing each factor as a power of $d + 2$.

## Main statements

* `latticeBoxFactor_le_add_two_pow`: `latticeBoxFactor k` is at most $(d + 2)^{2 (d + 1)^2}$ for
  $k \le d$.
* `latticeBoxFactor_mul_pow_le_exp`, `latticeBoxFactor_mul_two_pow_le_exp`,
  `pow_mul_two_pow_le_exp` and `two_pow_le_exp`: the factors of one step are at most
  $e^{2 (d + 2)^2 \log (d + 2)}$.
* `mul_pow_three_mul_log_add_le`: for $e < d$,
  $A (e + 2)^3 \log (e + 2) + A (d + 2)^2 \log (d + 2) \le A (d + 2)^3 \log (d + 2)$.
-/

public section

namespace ChangFreimanRuzsa

lemma log_add_two_pos {x : ℝ} (hx : 0 ≤ x) : 0 < Real.log (x + 2) :=
  Real.log_pos (by linarith)

/-- For $x \ge 0$, $2 (x + 2)^2 \log (x + 2) \le (x + 2)^3 \log (x + 2)$. -/
lemma two_mul_add_two_sq_mul_log_le {x : ℝ} (hx : 0 ≤ x) :
    2 * (x + 2) ^ 2 * Real.log (x + 2) ≤ (x + 2) ^ 3 * Real.log (x + 2) := by
  nlinarith [mul_nonneg (mul_nonneg hx (sq_nonneg (x + 2))) (log_add_two_pos hx).le]

/-- The map $x \mapsto (x + 2)^3 \log (x + 2)$ is monotone on $[0, \infty)$. -/
lemma add_two_pow_three_mul_log_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (x + 2) ^ 3 * Real.log (x + 2) ≤ (y + 2) ^ 3 * Real.log (y + 2) :=
  mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith) 3)
    (Real.log_le_log (by linarith) (by linarith)) (log_add_two_pos hx).le
    (pow_nonneg (by linarith) 3)

/-- If $n \le y$, then $(d + 2)^n \le e^{y \log (d + 2)}$. -/
lemma add_two_pow_le_exp_mul_log {d n : ℕ} {y : ℝ} (hny : (n : ℝ) ≤ y) :
    ((d : ℝ) + 2) ^ n ≤ Real.exp (y * Real.log ((d : ℝ) + 2)) := by
  rw [← Real.log_le_iff_le_exp (by positivity), Real.log_pow]
  exact mul_le_mul_of_nonneg_right hny (log_add_two_pos d.cast_nonneg).le

/-- For $k \le d$, `latticeBoxFactor k` is at most $(d + 2)^{2 (d + 1)^2}$. -/
lemma latticeBoxFactor_le_add_two_pow {k d : ℕ} (hkd : k ≤ d) :
    latticeBoxFactor k ≤ (d + 2) ^ (2 * (d + 1) ^ 2) := by
  rw [pow_mul (d + 2)]
  exact (latticeBoxFactor_le_pow k).trans
    ((Nat.pow_le_pow_left (by nlinarith : 4 * k + 1 ≤ (d + 2) ^ 2) _).trans
      (Nat.pow_le_pow_right (by positivity) (by nlinarith : (k + 2) * k ≤ (d + 1) ^ 2)))

/-- $2^d \le e^{(d + 2)^2 \log (d + 2)}$. -/
lemma two_pow_le_exp (d : ℕ) :
    (2 : ℝ) ^ d ≤ Real.exp (((d : ℝ) + 2) ^ 2 * Real.log ((d : ℝ) + 2)) :=
  (pow_le_pow_left₀ zero_le_two (by linarith [d.cast_nonneg (α := ℝ)]) d).trans
    (add_two_pow_le_exp_mul_log (by nlinarith))

/-- For $r \le d$, the factor `latticeBoxFactor (d - r)` $\cdot ((2r + 4)(2(3r + 1) + 1))^d$ of one
quotient step is at most $e^{2 (d + 2)^2 \log (d + 2)}$. -/
lemma latticeBoxFactor_mul_pow_le_exp {r d : ℕ} (hrd : r ≤ d) :
    (latticeBoxFactor (d - r) : ℝ) * ((2 * (r : ℝ) + 4) * (2 * (3 * (r : ℝ) + 1) + 1)) ^ d ≤
      Real.exp (2 * ((d : ℝ) + 2) ^ 2 * Real.log ((d : ℝ) + 2)) := by
  have hr : (r : ℝ) ≤ d := Nat.cast_le.mpr hrd
  calc (latticeBoxFactor (d - r) : ℝ) * ((2 * (r : ℝ) + 4) * (2 * (3 * (r : ℝ) + 1) + 1)) ^ d
      ≤ ((d : ℝ) + 2) ^ (2 * (d + 1) ^ 2) * (((d : ℝ) + 2) ^ 4) ^ d := by
        gcongr
        · exact_mod_cast latticeBoxFactor_le_add_two_pow (Nat.sub_le d r)
        · nlinarith [mul_le_mul hr hr (Nat.cast_nonneg r) (Nat.cast_nonneg d),
            pow_nonneg (Nat.cast_nonneg (α := ℝ) d) 3, pow_nonneg (Nat.cast_nonneg (α := ℝ) d) 4,
            Nat.cast_nonneg (α := ℝ) r]
    _ ≤ _ := by
        rw [← pow_mul, ← pow_add]
        exact add_two_pow_le_exp_mul_log (by push_cast; nlinarith)

/-- For $k \le d$, `latticeBoxFactor k` $\cdot 2^d \le e^{2 (d + 2)^2 \log (d + 2)}$. -/
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

/-- $(6d + 1)^d \cdot 2^d \le e^{(d + 2)^2 \log (d + 2)}$. -/
lemma pow_mul_two_pow_le_exp (d : ℕ) :
    (2 * (3 * (d : ℝ)) + 1) ^ d * (2 : ℝ) ^ d ≤
      Real.exp (((d : ℝ) + 2) ^ 2 * Real.log ((d : ℝ) + 2)) := by
  rw [← mul_pow]
  refine (pow_le_pow_left₀ (by positivity)
    (by nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) d) 3] :
      (2 * (3 * (d : ℝ)) + 1) * 2 ≤ ((d : ℝ) + 2) ^ 3) d).trans ?_
  rw [← pow_mul]
  exact add_two_pow_le_exp_mul_log (by push_cast; nlinarith)

/-- For $A \ge 0$ and $e < d$,
$A (e + 2)^3 \log (e + 2) + A (d + 2)^2 \log (d + 2) \le A (d + 2)^3 \log (d + 2)$. Indeed
$(e + 2)^3 \le (d + 1)^3$ and $(d + 1)^3 + (d + 2)^2 \le (d + 2)^3$. -/
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
