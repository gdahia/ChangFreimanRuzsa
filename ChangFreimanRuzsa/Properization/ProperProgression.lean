/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GAP.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import SumOfSetsInSeveralDimensions.FreimanDimension
import ChangFreimanRuzsa.FreimanDimension.CentralSection
import ChangFreimanRuzsa.Properization.BodyProgression
import ChangFreimanRuzsa.Properization.IteratedQuotient
import ChangFreimanRuzsa.GeometryOfNumbers.RealBox

/-!
# From a progression to a `t`-proper progression of dimension at most the Freiman dimension

Let `G` be an abelian group in which the multiples `n • a` with `n < N` of every nonzero `a` are
distinct, let `1 ≤ t`, and let a finite nonempty set `X` lie in a progression `P` of dimension `d`.
Write `R` for `freimanDim X`. If `exp (tProperExponent t R) * (8 * (d + 2) ^ 3) ^ d * P.size < N`,
then `X` lies in a `t`-proper progression of dimension at most `R` with at most that many points.
This is the argument of Section 1 of Green's notes *Progressions and convex geometry*, with the
dimension reduction of Bilu.

1. `P` lies in the convex progression with the origin and the steps of `P` whose body is the
   symmetric box `realBox (P.bound + 1)`, of volume `2 ^ d * P.size`.
2. `ConvexProgression.exists_tProper_superset` with `s = 2` gives a `2`-proper convex progression
   of dimension `m ≤ d` containing it.
3. `ConvexProgression.exists_superset_dim_le_freimanDim` passes to a convex progression of
   dimension `r ≤ R` containing `X`, whose body is a central section.
4. `ConvexProgression.exists_tProper_superset` with `s = 2 * t * (r + 1) * r! ^ 2` and
   `ConvexProgression.exists_tProperGAP_superset` give the `t`-proper progression.

## Main definitions

* `tProperExponent t r`: the logarithm of the loss of the last stage in dimension `r`.

## Main statements

* `exists_tProperGAP_subset_dim_le_freimanDim_of_subset_gap`: the passage from `P` to a
  `t`-proper progression of dimension at most `freimanDim X`.
-/

public section

namespace ChangFreimanRuzsa

open MeasureTheory Set SumOfSetsInSeveralDimensions
open scoped Finset Pointwise

/-- The logarithm of `(2 * t * (r + 1) * r! ^ 2 * (r + 2) ^ 2) ^ r * (3 * r! ^ 2) ^ r * r!`, the
factor lost in dimension `r` when a symmetric body is turned into a `t`-proper progression. -/
@[expose] noncomputable def tProperExponent (t r : ℕ) : ℝ :=
  Real.log (((2 * t * (r + 1) * r.factorial ^ 2 * (r + 2) ^ 2) ^ r * (3 * r.factorial ^ 2) ^ r *
    r.factorial : ℕ) : ℝ)

variable {t : ℕ}

private lemma one_le_two_mul_mul_factorial_sq (ht : 1 ≤ t) (r : ℕ) :
    1 ≤ 2 * t * (r + 1) * r.factorial ^ 2 :=
  Nat.one_le_iff_ne_zero.2 (by simp [Nat.factorial_ne_zero]; grind)

private lemma pow_le_pow_of_le {a b r R : ℕ} (hb : 1 ≤ b) (hab : a ≤ b) (hrR : r ≤ R) :
    a ^ r ≤ b ^ R :=
  (Nat.pow_le_pow_left hab r).trans (Nat.pow_le_pow_right hb hrR)

private lemma three_mul_factorial_sq_pow_le {r R : ℕ} (hrR : r ≤ R) :
    (3 * r.factorial ^ 2) ^ r ≤ (3 * R.factorial ^ 2) ^ R := by
  refine pow_le_pow_of_le (Nat.one_le_iff_ne_zero.2 (by simp [Nat.factorial_ne_zero])) ?_ hrR
  gcongr

private lemma tProperFactor_mono (ht : 1 ≤ t) {r R : ℕ} (hrR : r ≤ R) :
    (2 * t * (r + 1) * r.factorial ^ 2 * (r + 2) ^ 2) ^ r * (3 * r.factorial ^ 2) ^ r *
        r.factorial ≤
      (2 * t * (R + 1) * R.factorial ^ 2 * (R + 2) ^ 2) ^ R * (3 * R.factorial ^ 2) ^ R *
        R.factorial := by
  refine Nat.mul_le_mul (Nat.mul_le_mul (pow_le_pow_of_le ?_ ?_ hrR)
    (three_mul_factorial_sq_pow_le hrR)) (Nat.factorial_le hrR)
  · nlinarith [one_le_two_mul_mul_factorial_sq ht R]
  · gcongr

private lemma tProperFactor_pos (ht : 1 ≤ t) (r : ℕ) :
    0 < (2 * t * (r + 1) * r.factorial ^ 2 * (r + 2) ^ 2) ^ r * (3 * r.factorial ^ 2) ^ r *
      r.factorial := by
  have := one_le_two_mul_mul_factorial_sq ht r
  have := Nat.factorial_pos r
  positivity

lemma tProperExponent_nonneg (ht : 1 ≤ t) (r : ℕ) : 0 ≤ tProperExponent t r :=
  Real.log_nonneg (Nat.one_le_cast.2 (tProperFactor_pos ht r))

lemma tProperExponent_mono (ht : 1 ≤ t) {r R : ℕ} (hrR : r ≤ R) :
    tProperExponent t r ≤ tProperExponent t R :=
  Real.log_le_log (Nat.cast_pos.2 (tProperFactor_pos ht r))
    (Nat.cast_le.2 (tProperFactor_mono ht hrR))

/-- The exponential of `tProperExponent t r` is the product of the loss
`(s * (r + 2) ^ 2) ^ r` of the quotients with `s = 2 * t * (r + 1) * r! ^ 2` and the loss
`(3 * r! ^ 2) ^ r * r!` of `ConvexProgression.exists_tProperGAP_superset`. -/
private lemma exp_tProperExponent (ht : 1 ≤ t) (r : ℕ) :
    Real.exp (tProperExponent t r) =
      (((2 * t * (r + 1) * r.factorial ^ 2 : ℕ) : ℝ) * (r + 2) ^ 2) ^ r *
        ((3 * r.factorial ^ 2) ^ r * r.factorial : ℕ) := by
  rw [tProperExponent, Real.exp_log (Nat.cast_pos.2 (tProperFactor_pos ht r))]
  push_cast
  ring

variable {G : Type*} [AddCommGroup G] {N : ℕ}

/-! ## The convex progression of the box of a progression -/

private lemma isFullSymmetricBody_realBox_bound_add_one (P : GAP G) :
    IsFullSymmetricBody (realBox (P.bound + 1)) :=
  isFullSymmetricBody_realBox fun _ ↦ Nat.succ_pos _

/-- The convex progression with the origin and the steps of `P` and the box of half-widths
`P.bound i + 1`. The box is wider than the coefficient box `0 ≤ w ≤ P.bound`, so that it is a full
symmetric body even when some `P.bound i` is `0`, and its volume is `2 ^ P.dim * P.size`. -/
private def boxProgression (P : GAP G) : ConvexProgression G :=
  ⟨P.dim, P.origin, P.hom, (isFullSymmetricBody_realBox_bound_add_one P).toConvexBody⟩

private lemma dim_boxProgression (P : GAP G) : (boxProgression P).dim = P.dim := rfl

/-- A progression lies in the convex progression of its box. -/
private lemma mem_boxProgression (P : GAP G) {x : G} (hx : x ∈ P) : x ∈ boxProgression P := by
  obtain ⟨w, hw, rfl⟩ := GAP.mem_iff_exists_eval.1 hx
  refine ConvexProgression.mem_def.2
    ⟨fun i ↦ (w i : ℤ), ConvexBody.mem_latticePoints.2 ?_, (P.eval_eq_hom w).symm⟩
  refine mem_realBox.2 fun i ↦ ?_
  simpa using (Nat.cast_le (α := ℝ)).2 ((hw i).trans (Nat.le_succ _))

private lemma volume_real_body_boxProgression (P : GAP G) :
    volume.real ((boxProgression P).body : Set (Fin (boxProgression P).dim → ℝ)) =
      2 ^ P.dim * P.size := by
  rw [boxProgression, IsFullSymmetricBody.coe_toConvexBody, volume_real_realBox, GAP.size,
    Nat.cast_prod, ← Fin.prod_const, ← Finset.prod_mul_distrib]
  rfl

/-! ## The first stages -/

/-- The losses of the first stages: `(2 * (m + 2)) ^ m * ((2 * (d + 2) ^ 2) ^ d * 2 ^ d)` is at
most `(8 * (d + 2) ^ 3) ^ d` for `m ≤ d`. -/
private lemma pow_mul_pow_mul_two_pow_le {m d : ℕ} (hmd : m ≤ d) :
    (2 * ((m : ℝ) + 2)) ^ m * ((2 * ((d : ℝ) + 2) ^ 2) ^ d * 2 ^ d) ≤
      (8 * ((d : ℝ) + 2) ^ 3) ^ d := by
  calc (2 * ((m : ℝ) + 2)) ^ m * ((2 * ((d : ℝ) + 2) ^ 2) ^ d * 2 ^ d)
      ≤ (2 * ((d : ℝ) + 2)) ^ d * ((2 * ((d : ℝ) + 2) ^ 2) ^ d * 2 ^ d) := by
        gcongr
        refine (pow_le_pow_left₀ (by positivity) (by gcongr) m).trans
          (pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) d]) hmd)
    _ = (8 * ((d : ℝ) + 2) ^ 3) ^ d := by
        rw [← mul_pow, ← mul_pow]
        ring

/-- **The first stages.** Let a finite nonempty set `X` lie in a progression `P` of dimension `d`,
and let the multiples `n • a` with `n < N` of every nonzero `a` be distinct. If
`(8 * (d + 2) ^ 3) ^ d * P.size < N`, then `X` lies in a convex progression of dimension at most
`freimanDim X` whose body is a full symmetric body of volume at most
`(8 * (d + 2) ^ 3) ^ d * P.size`. -/
private lemma exists_convexProgression_of_subset_gap [DecidableEq G]
    (hG : ∀ a : G, a ≠ 0 → InjOn (fun n : ℕ ↦ n • a) (Iio N)) {X : Finset G} {P : GAP G}
    (hX : X.Nonempty) (hXP : X ⊆ P.toFinset)
    (hN : ((8 * (P.dim + 2) ^ 3) ^ P.dim * P.size : ℝ) < N) :
    ∃ Q : ConvexProgression G, Q.dim ≤ freimanDim X ∧
      IsFullSymmetricBody (Q.body : Set (Fin Q.dim → ℝ)) ∧ (∀ x ∈ X, x ∈ Q) ∧
        volume.real (Q.body : Set (Fin Q.dim → ℝ)) ≤ (8 * (P.dim + 2) ^ 3) ^ P.dim * P.size := by
  have hvol₀ := volume_real_body_boxProgression P
  have hN₀ : (2 * ((P.dim : ℝ) + 2) ^ 2) ^ P.dim *
      volume.real ((boxProgression P).body : Set (Fin (boxProgression P).dim → ℝ)) < N := by
    refine lt_of_le_of_lt ?_ hN
    rw [hvol₀]
    grw [← pow_mul_pow_mul_two_pow_le le_rfl]
    nlinarith [mul_le_mul_of_nonneg_right
      (one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) P.dim]) :
        (1 : ℝ) ≤ (2 * ((P.dim : ℝ) + 2)) ^ P.dim)
      (by positivity : (0 : ℝ) ≤ (2 * ((P.dim : ℝ) + 2) ^ 2) ^ P.dim * 2 ^ P.dim * P.size)]
  obtain ⟨Q₁, hm, hK₁, hQ₁, hPQ₁, hvol₁⟩ := (boxProgression P).exists_tProper_superset hG
    one_le_two (isFullSymmetricBody_realBox_bound_add_one P) hN₀
  obtain ⟨Q, hr, hK, hXQ, hvol⟩ := ConvexProgression.exists_superset_dim_le_freimanDim hK₁ hQ₁ hX
    fun x hx ↦ hPQ₁ x (mem_boxProgression P (ConvexProgression.mem_toFinset.1 (hXP hx)))
  refine ⟨Q, hr, hK, hXQ, ?_⟩
  grw [hvol, hvol₁, hvol₀]
  rw [dim_boxProgression] at hm ⊢
  grw [← pow_mul_pow_mul_two_pow_le hm]
  apply le_of_eq
  ring

/-! ## The last stage -/

/-- **The last stage.** Let `P` be a convex progression of dimension `r` whose body is a full
symmetric body. If `exp (tProperExponent t r) * vol P.body < N`, then `P` lies in a `t`-proper
progression of dimension at most `r` with at most `exp (tProperExponent t r) * vol P.body`
points. -/
private lemma exists_tProperGAP_superset_of_convexProgression [DecidableEq G] (ht : 1 ≤ t)
    (hG : ∀ a : G, a ≠ 0 → InjOn (fun n : ℕ ↦ n • a) (Iio N)) {P : ConvexProgression G}
    (hP : IsFullSymmetricBody (P.body : Set (Fin P.dim → ℝ)))
    (hN : Real.exp (tProperExponent t P.dim) * volume.real (P.body : Set (Fin P.dim → ℝ)) < N) :
    ∃ Q : GAP G, Q.Proper t ∧ (∀ x ∈ P, x ∈ Q) ∧ Q.dim ≤ P.dim ∧
      #Q.toFinset ≤
        Real.exp (tProperExponent t P.dim) * volume.real (P.body : Set (Fin P.dim → ℝ)) := by
  have hs := Nat.one_le_cast (α := ℝ).2 (one_le_two_mul_mul_factorial_sq ht P.dim)
  have hF : (1 : ℝ) ≤ ((3 * P.dim.factorial ^ 2) ^ P.dim * P.dim.factorial : ℕ) :=
    Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 (by simp [Nat.factorial_ne_zero]))
  rw [exp_tProperExponent ht] at hN ⊢
  obtain ⟨P', hr', hK', hP', hPP', hvol⟩ := P.exists_tProper_superset hG hs hP
    (lt_of_le_of_lt (by grw [← hF, mul_one]) hN)
  have hs' : (2 * t * P'.dim * P'.dim.factorial ^ 2 : ℝ) ≤
      ((2 * t * (P.dim + 1) * P.dim.factorial ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast (by gcongr; grind :
      2 * t * P'.dim * P'.dim.factorial ^ 2 ≤ 2 * t * (P.dim + 1) * P.dim.factorial ^ 2)
  obtain ⟨Q, hQ, hP'Q, hQdim, hQcard⟩ := ConvexProgression.exists_tProperGAP_superset hK' ht
    (hP'.mono hK'.zero_mem (by positivity) hs')
  refine ⟨Q, hQ, fun x hx ↦ hP'Q x (hPP' x hx), hQdim.trans hr', ?_⟩
  grw [hQcard, hvol]
  calc (3 * (P'.dim.factorial : ℝ) ^ 2) ^ P'.dim * P'.dim.factorial *
        ((((2 * t * (P.dim + 1) * P.dim.factorial ^ 2 : ℕ) : ℝ) * (P.dim + 2) ^ 2) ^ P.dim *
          volume.real (P.body : Set (Fin P.dim → ℝ)))
      ≤ ((3 * P.dim.factorial ^ 2) ^ P.dim * P.dim.factorial : ℕ) *
        ((((2 * t * (P.dim + 1) * P.dim.factorial ^ 2 : ℕ) : ℝ) * (P.dim + 2) ^ 2) ^ P.dim *
          volume.real (P.body : Set (Fin P.dim → ℝ))) := by
        gcongr
        exact_mod_cast Nat.mul_le_mul (three_mul_factorial_sq_pow_le hr')
          (Nat.factorial_le hr')
    _ = _ := by ring

/-! ## The passage to a `t`-proper progression -/

/-- **From a progression to a `t`-proper progression.** Let `1 ≤ t` and let the multiples `n • a`
with `n < N` of every nonzero `a` be distinct. Let a finite nonempty set `X` lie in a progression
`P` of dimension `d`, and write `B` for
`exp (tProperExponent t (freimanDim X)) * (8 * (d + 2) ^ 3) ^ d * P.size`. If `B < N`, then `X`
lies in a `t`-proper progression of dimension at most `freimanDim X` with at most `B` points. -/
lemma exists_tProperGAP_subset_dim_le_freimanDim_of_subset_gap [DecidableEq G] (ht : 1 ≤ t)
    (hG : ∀ a : G, a ≠ 0 → InjOn (fun n : ℕ ↦ n • a) (Iio N)) {X : Finset G} {P : GAP G}
    (hX : X.Nonempty) (hXP : X ⊆ P.toFinset)
    (hN : Real.exp (tProperExponent t (freimanDim X)) * (8 * (P.dim + 2) ^ 3) ^ P.dim * P.size <
      N) :
    ∃ Q : GAP G, Q.Proper t ∧ X ⊆ Q.toFinset ∧ Q.dim ≤ freimanDim X ∧
      #Q.toFinset ≤
        Real.exp (tProperExponent t (freimanDim X)) * (8 * (P.dim + 2) ^ 3) ^ P.dim * P.size := by
  rw [mul_assoc] at hN ⊢
  obtain ⟨R, hr, hK, hXR, hvol⟩ := exists_convexProgression_of_subset_gap hG hX hXP
    ((le_mul_of_one_le_left (by positivity)
      (Real.one_le_exp (tProperExponent_nonneg ht _))).trans_lt hN)
  have hT : Real.exp (tProperExponent t R.dim) * volume.real (R.body : Set (Fin R.dim → ℝ)) ≤
      Real.exp (tProperExponent t (freimanDim X)) * ((8 * (P.dim + 2) ^ 3) ^ P.dim * P.size) := by
    grw [hvol, tProperExponent_mono ht hr]
  obtain ⟨Q, hQ, hRQ, hQdim, hQcard⟩ :=
    exists_tProperGAP_superset_of_convexProgression ht hG hK (hT.trans_lt hN)
  exact ⟨Q, hQ, fun x hx ↦ ConvexProgression.mem_toFinset.2 (hRQ x (hXR x hx)), hQdim.trans hr,
    hQcard.trans hT⟩

/-- For `d ≤ c`, `(8 * (d + 2) ^ 3) ^ d ≤ exp (c * log (8 * (c + 2) ^ 3))`. -/
private lemma pow_le_exp_mul_log {d : ℕ} {c : ℝ} (hdc : d ≤ c) :
    (8 * ((d : ℝ) + 2) ^ 3) ^ d ≤ Real.exp (c * Real.log (8 * (c + 2) ^ 3)) := by
  rw [← Real.exp_log (by positivity : (0 : ℝ) < (8 * ((d : ℝ) + 2) ^ 3) ^ d), Real.log_pow]
  gcongr
  · exact Real.log_nonneg (by nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) d) 3,
      (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 2), Nat.cast_nonneg (α := ℝ) d])
  · linarith [Nat.cast_nonneg (α := ℝ) d]

/-- **From a progression to a `t`-proper progression**, with the loss written as an exponential.
Let `1 ≤ t`, let the multiples `n • a` with `n < N` of every nonzero `a` be distinct, and let a
finite nonempty set `X` lie in a progression `P` of dimension at most `c`. Write `E` for
`c * log (8 * (c + 2) ^ 3) + tProperExponent t (freimanDim X)`. If `exp (E + 1) * P.size ≤ N`, then
`X` lies in a `t`-proper progression of dimension at most `freimanDim X` with at most
`exp E * P.size` points. -/
lemma exists_tProperGAP_subset_dim_le_freimanDim_card_le_exp [DecidableEq G] (ht : 1 ≤ t)
    (hG : ∀ a : G, a ≠ 0 → InjOn (fun n : ℕ ↦ n • a) (Iio N)) {X : Finset G} {P : GAP G}
    (hX : X.Nonempty) (hXP : X ⊆ P.toFinset) {c : ℝ} (hPdim : P.dim ≤ c)
    (hN : Real.exp (c * Real.log (8 * (c + 2) ^ 3) + tProperExponent t (freimanDim X) + 1) *
      P.size ≤ N) :
    ∃ Q : GAP G, Q.Proper t ∧ X ⊆ Q.toFinset ∧ Q.dim ≤ freimanDim X ∧
      #Q.toFinset ≤
        Real.exp (c * Real.log (8 * (c + 2) ^ 3) + tProperExponent t (freimanDim X)) * P.size := by
  have hB : Real.exp (tProperExponent t (freimanDim X)) * (8 * (P.dim + 2) ^ 3) ^ P.dim * P.size ≤
      Real.exp (c * Real.log (8 * (c + 2) ^ 3) + tProperExponent t (freimanDim X)) * P.size := by
    grw [pow_le_exp_mul_log hPdim, ← Real.exp_add, add_comm (tProperExponent _ _)]
  obtain ⟨Q, hQ, hXQ, hQdim, hQcard⟩ := exists_tProperGAP_subset_dim_le_freimanDim_of_subset_gap ht
    hG hX hXP (hB.trans_lt (lt_of_lt_of_le (mul_lt_mul_of_pos_right
      (Real.exp_lt_exp.2 (lt_add_one _))
      (Nat.cast_pos.2 (P.nonempty.card_pos.trans_le P.card_le_size))) hN))
  exact ⟨Q, hQ, hXQ, hQdim, hQcard.trans hB⟩

end ChangFreimanRuzsa
