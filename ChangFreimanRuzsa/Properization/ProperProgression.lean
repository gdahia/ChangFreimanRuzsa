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
import ChangFreimanRuzsa.GAP.Relations
import ChangFreimanRuzsa.GeometryOfNumbers.RealBox
import ChangFreimanRuzsa.Properization.BodyProgression
import ChangFreimanRuzsa.Properization.IteratedQuotient

/-!
# From a progression to a `t`-proper progression of dimension at most the Freiman dimension

Let `G` be an abelian group in which the multiples `n • a` with `n < N` of every nonzero `a` are
distinct, let `1 ≤ t`, and let a finite nonempty set `X` lie in a progression `P` of dimension `d`.
Write `R` for `freimanDim X`. If `exp (tProperExponent t R) * (8 * (d + 2) ^ 3) ^ d * P.size < N`,
then `X` lies in a `t`-proper progression of dimension at most `R` with at most that many points.
This is the argument of Section 1 of Green's notes *Progressions and convex geometry*, with the
dimension reduction of Bilu.

1. The points of `P` are `P.origin + P.stepHom v` with `v` an integer point of a box `K₀ ⊆ ℝ ^ d`
   of volume at most `2 ^ d * P.size`.
2. `exists_injOn_latticePoints_smul` with `s = 2` replaces `K₀` by a full symmetric body
   `K₁ ⊆ ℝ ^ m`, `m ≤ d`, and a homomorphism injective on the integer points of `2 • K₁`.
3. `exists_isFullSymmetricBody_dim_le_freimanDim` passes to a central section `K₂ ⊆ ℝ ^ r` with
   `r ≤ R`, and every `x ∈ X` is `x₀ + ψ v` with `v` an integer point of `K₂`.
4. `exists_injOn_latticePoints_smul` with `s = 2 * t * (r + 1) * r! ^ 2` and
   `exists_tProperGAP_image_latticePoints_subset_of_injOn` give the `t`-proper progression.

## Main definitions

* `tProperExponent t r`: the logarithm of the loss of the last stage in dimension `r`.

## Main statements

* `exists_tProperGAP_subset_dim_le_freimanDim_of_subset_gap`: the passage from `P` to a
  `t`-proper progression of dimension at most `freimanDim X`.
-/

public section

namespace ChangFreimanRuzsa

open MeasureTheory Set SumOfSetsInSeveralDimensions
open scoped Pointwise

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
`(3 * r! ^ 2) ^ r * r!` of `exists_tProperGAP_image_latticePoints_subset_of_injOn`. -/
private lemma exp_tProperExponent (ht : 1 ≤ t) (r : ℕ) :
    Real.exp (tProperExponent t r) =
      (((2 * t * (r + 1) * r.factorial ^ 2 : ℕ) : ℝ) * (r + 2) ^ 2) ^ r *
        ((3 * r.factorial ^ 2) ^ r * r.factorial : ℕ) := by
  rw [tProperExponent, Real.exp_log (Nat.cast_pos.2 (tProperFactor_pos ht r))]
  push_cast
  ring

variable {G : Type*} [AddCommGroup G] {N : ℕ}

/-! ## The first stages -/

/-- The points of a progression `P` are `P.origin + P.stepHom v` with `v` an integer point of the
box of half-widths `P.length i - 1`. -/
private lemma exists_mem_latticePoints_realBox_of_mem [DecidableEq G] {P : GAP G} {x : G}
    (hx : x ∈ P.toFinset) :
    ∃ v ∈ latticePoints (realBox fun i ↦ P.length i - 1), x = P.origin + stepsHom P.step v := by
  obtain ⟨c, hc, rfl⟩ := (P.mem_toFinset_iff_exists_intCoeffs).1 hx
  refine ⟨c, ?_, rfl⟩
  rw [mem_latticePoints, mem_realBox]
  intro i
  rw [intVectorToReal_apply]
  have h : |c i| ≤ ((P.length i - 1 : ℕ) : ℤ) := by grind [abs_le, P.length_pos i]
  exact_mod_cast h

private lemma volume_real_realBox_length_sub_one_le (P : GAP G) :
    volume.real (realBox fun i ↦ P.length i - 1) ≤ 2 ^ P.dim * P.size := by
  rw [volume_real_realBox, P.size_eq_prod_length, Nat.cast_prod, ← Fin.prod_const,
    ← Finset.prod_mul_distrib]
  gcongr with i
  exact_mod_cast Nat.sub_le _ _

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
`(8 * (d + 2) ^ 3) ^ d * P.size < N`, then there are a full symmetric body `K ⊆ ℝ ^ r` with
`r ≤ freimanDim X` and `vol K ≤ (8 * (d + 2) ^ 3) ^ d * P.size`, a homomorphism `ψ` and a point
`x₀` such that every point of `X` is `x₀ + ψ v` with `v` an integer point of `K`. -/
private lemma exists_isFullSymmetricBody_of_subset_gap [DecidableEq G]
    (hG : ∀ a : G, a ≠ 0 → InjOn (fun n : ℕ ↦ n • a) (Iio N)) {X : Finset G} {P : GAP G}
    (hX : X.Nonempty) (hXP : X ⊆ P.toFinset)
    (hN : ((8 * (P.dim + 2) ^ 3) ^ P.dim * P.size : ℝ) < N) :
    ∃ (r : ℕ) (K : Set (Fin r → ℝ)) (ψ : (Fin r → ℤ) →+ G) (x₀ : G), r ≤ freimanDim X ∧
      IsFullSymmetricBody K ∧ (∀ x ∈ X, ∃ v ∈ latticePoints K, x = x₀ + ψ v) ∧
      volume.real K ≤ (8 * (P.dim + 2) ^ 3) ^ P.dim * P.size := by
  have hvol₀ := volume_real_realBox_length_sub_one_le P
  have hK₀ := isFullSymmetricBody_realBox (L := fun i ↦ P.length i - 1)
    (fun i ↦ by grind [P.one_lt_length i])
  have hN₀ : (2 * ((P.dim : ℝ) + 2) ^ 2) ^ P.dim * volume.real (realBox fun i ↦ P.length i - 1) <
      N := by
    refine lt_of_le_of_lt ?_ hN
    grw [hvol₀, ← pow_mul_pow_mul_two_pow_le le_rfl]
    nlinarith [mul_le_mul_of_nonneg_right
      (one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) P.dim]) :
        (1 : ℝ) ≤ (2 * ((P.dim : ℝ) + 2)) ^ P.dim)
      (by positivity : (0 : ℝ) ≤ (2 * ((P.dim : ℝ) + 2) ^ 2) ^ P.dim * 2 ^ P.dim * P.size)]
  obtain ⟨m, K₁, ψ₁, hm, hK₁, hψ₁, himg, hvol₁⟩ :=
    exists_injOn_latticePoints_smul hG one_le_two hK₀ (stepsHom P.step) hN₀
  have hXK₁ (x : G) (hx : x ∈ X) : ∃ v ∈ latticePoints K₁, x = P.origin + ψ₁ v := by
    obtain ⟨v, hv, rfl⟩ := exists_mem_latticePoints_realBox_of_mem (hXP hx)
    obtain ⟨w, hw, hwv⟩ := himg ⟨v, hv, rfl⟩
    exact ⟨w, hw, by rw [hwv]⟩
  obtain ⟨x₀, hx₀⟩ := hX
  obtain ⟨r, K, ψ, hr, hK, hXK, hvol⟩ :=
    exists_isFullSymmetricBody_dim_le_freimanDim hK₁ hψ₁ hXK₁ hx₀
  refine ⟨r, K, ψ, x₀, hr, hK, hXK, ?_⟩
  grw [hvol, hvol₁, hvol₀, ← pow_mul_pow_mul_two_pow_le hm]
  apply le_of_eq
  ring

/-! ## The last stage -/

/-- **The last stage.** Let `K ⊆ ℝ ^ r` be a full symmetric body and let every point of `X` be
`x₀ + ψ v` with `v` an integer point of `K`. If `exp (tProperExponent t r) * vol K < N`, then `X`
lies in a `t`-proper progression of dimension at most `r` with at most
`exp (tProperExponent t r) * vol K` points. -/
private lemma exists_tProperGAP_of_isFullSymmetricBody [DecidableEq G] (ht : 1 ≤ t)
    (hG : ∀ a : G, a ≠ 0 → InjOn (fun n : ℕ ↦ n • a) (Iio N)) {r : ℕ} {K : Set (Fin r → ℝ)}
    (hK : IsFullSymmetricBody K) (ψ : (Fin r → ℤ) →+ G) {X : Finset G} {x₀ : G}
    (hX : ∀ x ∈ X, ∃ v ∈ latticePoints K, x = x₀ + ψ v)
    (hN : Real.exp (tProperExponent t r) * volume.real K < N) :
    ∃ Q : GAP G, (t • Q).Proper ∧ X ⊆ Q.toFinset ∧ Q.dim ≤ r ∧
      Q.toFinset.card ≤ Real.exp (tProperExponent t r) * volume.real K := by
  have hs := Nat.one_le_cast (α := ℝ).2 (one_le_two_mul_mul_factorial_sq ht r)
  have hF : (1 : ℝ) ≤ ((3 * r.factorial ^ 2) ^ r * r.factorial : ℕ) :=
    Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 (by simp [Nat.factorial_ne_zero]))
  rw [exp_tProperExponent ht] at hN ⊢
  obtain ⟨r', K', ψ', hr', hK', hψ', himg, hvol⟩ := exists_injOn_latticePoints_smul hG hs hK ψ
    (lt_of_le_of_lt (by grw [← hF, mul_one]) hN)
  have hs' : |(2 * t * r' * r'.factorial ^ 2 : ℝ)| ≤
      |((2 * t * (r + 1) * r.factorial ^ 2 : ℕ) : ℝ)| := by
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact_mod_cast (by gcongr; grind :
      2 * t * r' * r'.factorial ^ 2 ≤ 2 * t * (r + 1) * r.factorial ^ 2)
  obtain ⟨Q, hQ, hQimg, hQdim, hQcard⟩ := exists_tProperGAP_image_latticePoints_subset_of_injOn hK'
    ht (hψ'.mono (latticePoints_mono (hK'.smul_subset_smul hs')))
  refine ⟨Q.shift x₀, (GAP.proper_nsmul_shift_iff t Q x₀).2 hQ, ?_, hQdim.trans hr', ?_⟩
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := hX x hx
    rw [GAP.toFinset_shift, Finset.mem_image]
    exact ⟨ψ v, hQimg (himg ⟨v, hv, rfl⟩), add_comm _ _⟩
  · grw [GAP.toFinset_shift, Finset.card_image_le, hQcard, hvol]
    calc (3 * (r'.factorial : ℝ) ^ 2) ^ r' * r'.factorial *
          ((((2 * t * (r + 1) * r.factorial ^ 2 : ℕ) : ℝ) * (r + 2) ^ 2) ^ r * volume.real K)
        ≤ ((3 * r.factorial ^ 2) ^ r * r.factorial : ℕ) *
          ((((2 * t * (r + 1) * r.factorial ^ 2 : ℕ) : ℝ) * (r + 2) ^ 2) ^ r *
            volume.real K) := by
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
    ∃ Q : GAP G, (t • Q).Proper ∧ X ⊆ Q.toFinset ∧ Q.dim ≤ freimanDim X ∧
      Q.toFinset.card ≤
        Real.exp (tProperExponent t (freimanDim X)) * (8 * (P.dim + 2) ^ 3) ^ P.dim * P.size := by
  rw [mul_assoc] at hN ⊢
  obtain ⟨r, K, ψ, x₀, hr, hK, hXK, hvol⟩ := exists_isFullSymmetricBody_of_subset_gap hG hX hXP
    ((le_mul_of_one_le_left (by positivity)
      (Real.one_le_exp (tProperExponent_nonneg ht _))).trans_lt hN)
  have hT : Real.exp (tProperExponent t r) * volume.real K ≤
      Real.exp (tProperExponent t (freimanDim X)) * ((8 * (P.dim + 2) ^ 3) ^ P.dim * P.size) := by
    grw [hvol, tProperExponent_mono ht hr]
  obtain ⟨Q, hQ, hXQ, hQdim, hQcard⟩ :=
    exists_tProperGAP_of_isFullSymmetricBody ht hG hK ψ hXK (hT.trans_lt hN)
  exact ⟨Q, hQ, hXQ, hQdim.trans hr, hQcard.trans hT⟩

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
    ∃ Q : GAP G, (t • Q).Proper ∧ X ⊆ Q.toFinset ∧ Q.dim ≤ freimanDim X ∧
      Q.toFinset.card ≤
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
