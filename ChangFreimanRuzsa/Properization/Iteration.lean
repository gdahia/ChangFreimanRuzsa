/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GAP.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import ChangFreimanRuzsa.Properization.ExponentialBounds
import ChangFreimanRuzsa.Properization.ShortRelations

/-!
# Iterated properization

Let `P` be a GAP of dimension `d` in an abelian group in which the multiples `n • a` with `n < N`
of every nonzero `a` are distinct, with `N` large compared with `#P.toFinset`, and let `2 ≤ t`. Each
application of `GAP.proper_nsmul_or_exists_gap_dim_lt` costs a factor
`exp (2 * (d + 2) ^ 2 * log (d + 2) + d * log (t / 2))` and either finds that the progression is
`t`-proper or lowers its dimension. Iterating proves that `P` lies in a `t`-proper GAP of dimension
at most `d` and of size at most
`exp (2 * (d + 2) ^ 3 * log (d + 2) + (d + 2) ^ 2 * log (t / 2)) * #P.toFinset`.

## Main definitions

* `properizationExponent`: the exponent `2 * (d + 2) ^ 3 * log (d + 2)` in the size bound of
  properization for `t = 2`.
* `tProperExponent`: the additional exponent `(d + 2) ^ 2 * log (t / 2)` for general `t`.

## Main statements

* `exists_tProperGAP_toFinset_subset_dim_le_card_le_of_injOn_nsmul`: the iterated statement.
* `exists_tProperGAP_zmod_toFinset_subset_dim_le_card_le` and
  `exists_tProperGAP_toFinset_subset_dim_le_card_le_of_isAddTorsionFree`: the statements in
  `ZMod q` for prime `q` and in torsion-free groups.
-/

@[expose] public section

namespace ChangFreimanRuzsa

noncomputable section

variable {G : Type*} [AddCommGroup G]

/-- The exponent `2 * (d + 2) ^ 3 * log (d + 2)` in the size bound of properization for `t = 2`. -/
def properizationExponent (d : ℝ) : ℝ := 2 * (d + 2) ^ 3 * Real.log (d + 2)

lemma properizationExponent_nonneg {d : ℝ} (hd : 0 ≤ d) : 0 ≤ properizationExponent d :=
  mul_nonneg (mul_nonneg zero_le_two (pow_nonneg (by linarith) 3)) (log_add_two_pos hd).le

lemma properizationExponent_mono {d d' : ℝ} (hd : 0 ≤ d) (hdd' : d ≤ d') :
    properizationExponent d ≤ properizationExponent d' := by
  rw [properizationExponent, properizationExponent, mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (add_two_pow_three_mul_log_le hd hdd') zero_le_two

/-- For `0 ≤ x`, `2 * (x + 2) ^ 2 * log (x + 2)`, the exponent of one step of properization, is at
most `properizationExponent x`. -/
lemma mul_sq_mul_log_le_properizationExponent {x : ℝ} (hx : 0 ≤ x) :
    2 * (x + 2) ^ 2 * Real.log (x + 2) ≤ properizationExponent x := by
  rw [properizationExponent]
  nlinarith [two_mul_add_two_sq_mul_log_le hx,
    mul_nonneg (pow_nonneg (by linarith : 0 ≤ x + 2) 3) (log_add_two_pos hx).le]

/-- The exponent `(d + 2) ^ 2 * log (t / 2)` that `t`-properness adds to
`properizationExponent d`. It vanishes for `t = 2`. -/
def tProperExponent (t : ℕ) (d : ℝ) : ℝ := (d + 2) ^ 2 * Real.log ((t : ℝ) / 2)

@[simp] lemma tProperExponent_two (d : ℝ) : tProperExponent 2 d = 0 := by
  simp [tProperExponent]

lemma tProperExponent_nonneg {t : ℕ} (ht : 2 ≤ t) (d : ℝ) : 0 ≤ tProperExponent t d :=
  mul_nonneg (sq_nonneg _) (log_div_two_nonneg ht)

lemma tProperExponent_mono {t : ℕ} (ht : 2 ≤ t) {d d' : ℝ} (hd : 0 ≤ d) (hdd' : d ≤ d') :
    tProperExponent t d ≤ tProperExponent t d' :=
  mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (by linarith) 2)
    (log_div_two_nonneg ht)

/-- For `e < d`, `tProperExponent t e + d * log (t / 2) ≤ tProperExponent t d`. Indeed
`(e + 2) ^ 2 ≤ (d + 1) ^ 2` and `(d + 1) ^ 2 + d ≤ (d + 2) ^ 2`. -/
lemma tProperExponent_add_mul_log_le {t e d : ℕ} (ht : 2 ≤ t) (hed : e < d) :
    tProperExponent t e + d * Real.log ((t : ℝ) / 2) ≤ tProperExponent t d := by
  rw [tProperExponent, tProperExponent, ← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ (log_div_two_nonneg ht)
  nlinarith [(Nat.cast_le (α := ℝ)).2 (Nat.succ_le_of_lt hed), Nat.cast_nonneg (α := ℝ) e,
    Nat.cast_nonneg (α := ℝ) d, Nat.cast_succ (R := ℝ) e]

/-- If `exp (properizationExponent d + tProperExponent t d) * #P.toFinset ≤ N`, then `P` satisfies
the hypothesis `(2 * (t * d) + 1) ^ d * #P.toFinset < N` of
`GAP.proper_nsmul_or_exists_gap_dim_lt`. -/
lemma GAP.mul_card_lt_of_exp_mul_card_le [DecidableEq G] {N t : ℕ} {P : GAP G} (ht : 2 ≤ t)
    (hcard : Real.exp (properizationExponent P.dim + tProperExponent t P.dim) * P.toFinset.card ≤
      N) :
    (2 * (t * P.dim) + 1) ^ P.dim * P.toFinset.card < N := by
  have hd := Nat.cast_nonneg (α := ℝ) P.dim
  have hexp : Real.exp (((P.dim : ℝ) + 2) ^ 2 * Real.log ((P.dim : ℝ) + 2) +
      P.dim * Real.log ((t : ℝ) / 2)) <
      Real.exp (properizationExponent P.dim + tProperExponent t P.dim) := by
    rw [Real.exp_lt_exp]
    have hlog : (P.dim : ℝ) * Real.log ((t : ℝ) / 2) ≤ tProperExponent t P.dim :=
      mul_le_mul_of_nonneg_right (by nlinarith) (log_div_two_nonneg ht)
    linarith [mul_sq_mul_log_le_properizationExponent hd,
      mul_pos (pow_pos (by positivity : (0 : ℝ) < (P.dim : ℝ) + 2) 2) (log_add_two_pos hd)]
  exact_mod_cast ((mul_le_mul_of_nonneg_right (two_mul_mul_add_one_pow_le_exp ht P.dim)
    (Nat.cast_nonneg _)).trans_lt (mul_lt_mul_of_pos_right hexp
      (mod_cast P.nonempty.card_pos))).trans_le hcard

/-- For `e < d` and `0 ≤ x`, writing `E` for `properizationExponent` and `T` for
`tProperExponent t`,
`exp (E e + T e) * (exp (2 * (d + 2) ^ 2 * log (d + 2) + d * log (t / 2)) * x)` is at most
`exp (E d + T d) * x`. -/
lemma exp_mul_exp_mul_le_of_lt {t e d : ℕ} (ht : 2 ≤ t) (hed : e < d) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (properizationExponent e + tProperExponent t e) *
        (Real.exp (2 * ((d : ℝ) + 2) ^ 2 * Real.log ((d : ℝ) + 2) +
          d * Real.log ((t : ℝ) / 2)) * x) ≤
      Real.exp (properizationExponent d + tProperExponent t d) * x := by
  rw [← mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hx
  unfold properizationExponent
  linarith [mul_pow_three_mul_log_add_le (A := 2) zero_le_two hed,
    tProperExponent_add_mul_log_le ht hed]

variable [DecidableEq G]

/-- Let `P` be a GAP of dimension `d` in an abelian group in which the multiples `n • a` with
`n < N` of every nonzero `a` are distinct, and let `2 ≤ t`. Write `E d` for
`properizationExponent d + tProperExponent t d` and suppose `exp (E d) * #P.toFinset ≤ N`. Then `P`
lies in a `t`-proper GAP of dimension at most `d` and of size at most `exp (E d) * #P.toFinset`.
The proof iterates `GAP.proper_nsmul_or_exists_gap_dim_lt`: each step costs a factor
`exp (2 * (d + 2) ^ 2 * log (d + 2) + d * log (t / 2))` and either finds that the progression is
`t`-proper or lowers the dimension. -/
lemma exists_tProperGAP_toFinset_subset_dim_le_card_le_of_injOn_nsmul {N t : ℕ} (P : GAP G)
    (ht : 2 ≤ t) (hG : ∀ a : G, a ≠ 0 → Set.InjOn (fun n : ℕ ↦ n • a) (Set.Iio N))
    (hcard : Real.exp (properizationExponent P.dim + tProperExponent t P.dim) * P.toFinset.card ≤
      N) :
    ∃ Q : GAP G, (t • Q).Proper ∧ P.toFinset ⊆ Q.toFinset ∧ Q.dim ≤ P.dim ∧
      Q.toFinset.card ≤
        Real.exp (properizationExponent P.dim + tProperExponent t P.dim) * P.toFinset.card := by
  induction hd : P.dim using Nat.strong_induction_on generalizing P with
  | h d ih =>
    subst hd
    rcases GAP.proper_nsmul_or_exists_gap_dim_lt ht hG
      (GAP.mul_card_lt_of_exp_mul_card_le ht hcard) with hP | ⟨Q, hPQ, hdim, hQcard⟩
    · refine ⟨P, hP, subset_rfl, le_rfl, le_mul_of_one_le_left (Nat.cast_nonneg _) ?_⟩
      exact Real.one_le_exp (add_nonneg (properizationExponent_nonneg (Nat.cast_nonneg _))
        (tProperExponent_nonneg ht _))
    · have hQbound := mul_le_mul_of_nonneg_left hQcard
        (Real.exp_pos (properizationExponent Q.dim + tProperExponent t Q.dim)).le
      obtain ⟨R, hR, hQR, hRdim, hRcard⟩ := ih Q.dim hdim Q
        (hQbound.trans ((exp_mul_exp_mul_le_of_lt ht hdim (by positivity)).trans hcard)) rfl
      exact ⟨R, hR, hPQ.trans hQR, hRdim.trans hdim.le,
        hRcard.trans (hQbound.trans (exp_mul_exp_mul_le_of_lt ht hdim (by positivity)))⟩

/-- Properization in `ZMod q` for a prime `q` and `2 ≤ t`, with
`exp (properizationExponent d + tProperExponent t d) * #P.toFinset ≤ q`. -/
lemma exists_tProperGAP_zmod_toFinset_subset_dim_le_card_le {q t : ℕ} (P : GAP (ZMod q))
    (hq : Nat.Prime q) (ht : 2 ≤ t)
    (hcard : Real.exp (properizationExponent P.dim + tProperExponent t P.dim) * P.toFinset.card ≤
      q) :
    ∃ Q : GAP (ZMod q), (t • Q).Proper ∧ P.toFinset ⊆ Q.toFinset ∧ Q.dim ≤ P.dim ∧
      Q.toFinset.card ≤
        Real.exp (properizationExponent P.dim + tProperExponent t P.dim) * P.toFinset.card :=
  exists_tProperGAP_toFinset_subset_dim_le_card_le_of_injOn_nsmul P ht
    (fun _ ha ↦ GAP.injOn_nsmul_of_prime hq ha) hcard

/-- Properization in a torsion-free group, such as `ℤ`, for `2 ≤ t`, with no condition on
`#P.toFinset`. -/
lemma exists_tProperGAP_toFinset_subset_dim_le_card_le_of_isAddTorsionFree [IsAddTorsionFree G]
    {t : ℕ} (P : GAP G) (ht : 2 ≤ t) :
    ∃ Q : GAP G, (t • Q).Proper ∧ P.toFinset ⊆ Q.toFinset ∧ Q.dim ≤ P.dim ∧
      Q.toFinset.card ≤
        Real.exp (properizationExponent P.dim + tProperExponent t P.dim) * P.toFinset.card :=
  exists_tProperGAP_toFinset_subset_dim_le_card_le_of_injOn_nsmul P ht
    (fun _ ha ↦ GAP.injOn_nsmul_of_isAddTorsionFree _ ha) (Nat.le_ceil _)

end

end ChangFreimanRuzsa
