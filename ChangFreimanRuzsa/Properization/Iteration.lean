/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GAP.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import ChangFreimanRuzsa.Properization.ExponentialBounds
import ChangFreimanRuzsa.Properization.ShortRelations

/-!
# Iterated properization

Let `P` be a GAP of dimension `d` in an abelian group in which the multiples `n • a` with `n < N`
of every nonzero `a` are distinct, with `N` large compared with `#P.carrier`. Each application of
`GAP.proper_add_self_or_exists_gap_dim_lt` costs a factor `exp (2 * (d + 2) ^ 2 * log (d + 2))`
and either finds that the progression is `2`-proper or lowers its dimension. Iterating proves that
`P` lies in a `2`-proper GAP of dimension at most `d` and of size at most
`exp (2 * (d + 2) ^ 3 * log (d + 2)) * #P.carrier`.

## Main definitions

* `properizationExponent`: the exponent `2 * (d + 2) ^ 3 * log (d + 2)` in the size bound of
  properization.

## Main statements

* `exists_twoProperGAP_carrier_subset_dim_le_card_le_of_injOn_nsmul`: the iterated statement.
* `exists_twoProperGAP_zmod_carrier_subset_dim_le_card_le` and
  `exists_twoProperGAP_carrier_subset_dim_le_card_le_of_isAddTorsionFree`: the statements in
  `ZMod q` for prime `q` and in torsion-free groups.
-/

@[expose] public section

namespace ChangFreimanRuzsa

noncomputable section

variable {G : Type*} [AddCommGroup G]

/-- The exponent `2 * (d + 2) ^ 3 * log (d + 2)` in the size bound of properization. -/
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

/-- If `exp (properizationExponent d) * #P.carrier ≤ N`, then `P` satisfies the hypothesis
`(2 * (2 * d) + 1) ^ d * #P.carrier < N` of `GAP.proper_add_self_or_exists_gap_dim_lt`. -/
lemma GAP.mul_card_lt_of_exp_mul_card_le [DecidableEq G] {N : ℕ} {P : GAP G}
    (hcard : Real.exp (properizationExponent P.dim) * P.carrier.card ≤ N) :
    (2 * (2 * P.dim) + 1) ^ P.dim * P.carrier.card < N := by
  have hexp : Real.exp (((P.dim : ℝ) + 2) ^ 2 * Real.log ((P.dim : ℝ) + 2)) <
      Real.exp (properizationExponent P.dim) := by
    rw [Real.exp_lt_exp]
    linarith [mul_sq_mul_log_le_properizationExponent (Nat.cast_nonneg (α := ℝ) P.dim),
      mul_pos (pow_pos (by positivity : (0 : ℝ) < (P.dim : ℝ) + 2) 2)
        (log_add_two_pos (Nat.cast_nonneg (α := ℝ) P.dim))]
  exact_mod_cast ((mul_le_mul_of_nonneg_right (two_mul_two_mul_add_one_pow_le_exp P.dim)
    (Nat.cast_nonneg _)).trans_lt (mul_lt_mul_of_pos_right hexp
      (mod_cast P.nonempty.card_pos))).trans_le hcard

/-- For `e < d` and `0 ≤ x`, writing `E` for `properizationExponent`,
`exp (E e) * (exp (2 * (d + 2) ^ 2 * log (d + 2)) * x) ≤ exp (E d) * x`. -/
lemma exp_mul_exp_mul_le_of_lt {e d : ℕ} (hed : e < d) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (properizationExponent e) *
        (Real.exp (2 * ((d : ℝ) + 2) ^ 2 * Real.log ((d : ℝ) + 2)) * x) ≤
      Real.exp (properizationExponent d) * x := by
  rw [← mul_assoc, ← Real.exp_add]
  gcongr
  exact mul_pow_three_mul_log_add_le zero_le_two hed

variable [DecidableEq G]

/-- Let `P` be a GAP of dimension `d` in an abelian group in which the multiples `n • a` with
`n < N` of every nonzero `a` are distinct. Write `E d = 2 * (d + 2) ^ 3 * log (d + 2)` for
`properizationExponent d` and suppose `exp (E d) * #P.carrier ≤ N`. Then `P` lies in a `2`-proper
GAP of dimension at most `d` and of size at most `exp (E d) * #P.carrier`. The proof iterates
`GAP.proper_add_self_or_exists_gap_dim_lt`: each step costs a factor
`exp (2 * (d + 2) ^ 2 * log (d + 2))` and either finds that the progression is `2`-proper or
lowers the dimension. -/
lemma exists_twoProperGAP_carrier_subset_dim_le_card_le_of_injOn_nsmul {N : ℕ} (P : GAP G)
    (hG : ∀ a : G, a ≠ 0 → Set.InjOn (fun n : ℕ ↦ n • a) (Set.Iio N))
    (hcard : Real.exp (properizationExponent P.dim) * P.carrier.card ≤ N) :
    ∃ Q : GAP G, (Q + Q).Proper ∧ P.carrier ⊆ Q.carrier ∧ Q.dim ≤ P.dim ∧
      Q.carrier.card ≤ Real.exp (properizationExponent P.dim) * P.carrier.card := by
  induction hd : P.dim using Nat.strong_induction_on generalizing P with
  | h d ih =>
    subst hd
    rcases GAP.proper_add_self_or_exists_gap_dim_lt hG
      (GAP.mul_card_lt_of_exp_mul_card_le hcard) with hP | ⟨Q, hPQ, hdim, hQcard⟩
    · refine ⟨P, hP, subset_rfl, le_rfl, le_mul_of_one_le_left (Nat.cast_nonneg _) ?_⟩
      exact Real.one_le_exp (properizationExponent_nonneg (Nat.cast_nonneg _))
    · have hQbound := mul_le_mul_of_nonneg_left hQcard
        (Real.exp_pos (properizationExponent Q.dim)).le
      obtain ⟨R, hR, hQR, hRdim, hRcard⟩ := ih Q.dim hdim Q
        (hQbound.trans ((exp_mul_exp_mul_le_of_lt hdim (by positivity)).trans hcard)) rfl
      exact ⟨R, hR, hPQ.trans hQR, hRdim.trans hdim.le,
        hRcard.trans (hQbound.trans (exp_mul_exp_mul_le_of_lt hdim (by positivity)))⟩

/-- Properization in `ZMod q` for a prime `q` with
`exp (properizationExponent d) * #P.carrier ≤ q`. -/
lemma exists_twoProperGAP_zmod_carrier_subset_dim_le_card_le {q : ℕ} (P : GAP (ZMod q))
    (hq : Nat.Prime q) (hcard : Real.exp (properizationExponent P.dim) * P.carrier.card ≤ q) :
    ∃ Q : GAP (ZMod q), (Q + Q).Proper ∧ P.carrier ⊆ Q.carrier ∧ Q.dim ≤ P.dim ∧
      Q.carrier.card ≤ Real.exp (properizationExponent P.dim) * P.carrier.card :=
  exists_twoProperGAP_carrier_subset_dim_le_card_le_of_injOn_nsmul P
    (fun _ ha ↦ GAP.injOn_nsmul_of_prime hq ha) hcard

/-- Properization in a torsion-free group, such as `ℤ`, with no condition on `#P.carrier`. -/
lemma exists_twoProperGAP_carrier_subset_dim_le_card_le_of_isAddTorsionFree [IsAddTorsionFree G]
    (P : GAP G) :
    ∃ Q : GAP G, (Q + Q).Proper ∧ P.carrier ⊆ Q.carrier ∧ Q.dim ≤ P.dim ∧
      Q.carrier.card ≤ Real.exp (properizationExponent P.dim) * P.carrier.card :=
  exists_twoProperGAP_carrier_subset_dim_le_card_le_of_injOn_nsmul P
    (fun _ ha ↦ GAP.injOn_nsmul_of_isAddTorsionFree _ ha) (Nat.le_ceil _)

end

end ChangFreimanRuzsa
