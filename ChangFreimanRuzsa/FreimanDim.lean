/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.FreimanDimension.CoordinateReduction
public import ChangFreimanRuzsa.Int
import ChangFreimanRuzsa.ExponentBounds
import ChangFreimanRuzsa.Properization.ShortRelations

/-!
# Chang's theorem with dimension at most the Freiman dimension

Let `q` be a prime, let `2 ≤ t` and let `X : Finset (ZMod q)` satisfy `#(X + X) ≤ κ * #X`. Write `T`
for `tProperExponent t (freimanDim X)`, `F` for `freimanDimExponent κ` and `d` for `bohrGAPDim κ`.
If `256 * d ≤ #X` and `exp (F + T) * #X ≤ q`, then `X` lies in a `t`-proper generalized arithmetic
progression of dimension at most `freimanDim X` and of size at most `exp (F + T) * #X`. A finite
nonempty set `X : Finset ℤ` with `#(X + X) ≤ κ * #X` lies in a `t`-proper progression of dimension
at most `freimanDim X` and of size at most `exp (E + T) * #X`, where `E` is
`intFreimanDimExponent κ`.

Write `c` for `containerExponent κ`. In `ZMod q` the proof has three stages.
`exists_gap_zmod_subset_dim_le_card_le` puts `X` in a progression of dimension at most `c` and of
size at most `exp c * #X`, `exists_tProperGAP_toFinset_subset_dim_le_card_le_of_injOn_nsmul` with
`t = 2` replaces that progression by a `2`-proper one, and
`exists_tProperGAP_dim_le_freimanDim_of_injOn_nsmul` replaces the `2`-proper progression by a
`t`-proper one of dimension at most `freimanDim X`. Only the last stage depends on `t`. For sets of
integers, `exists_tProperGAP_dim_le_freimanDim_of_isAddTorsionFree` is applied to the `2`-proper
progression of `exists_tProperGAP_of_small_sumset`.

## Main definitions

* `freimanDimExponent κ`: the part of the exponent in the size bound of the progression in `ZMod q`
  that does not depend on `t`.
* `intFreimanDimExponent κ`: the part of the exponent in the size bound of the progression for sets
  of integers that does not depend on `t`.

## Main statements

* `exists_tProperGAP_zmod_dim_le_freimanDim`: Chang's theorem in `ZMod q` with dimension at most
  `freimanDim X`.
* `exists_tProperGAP_int_dim_le_freimanDim`: Chang's theorem for sets of integers with dimension
  at most `freimanDim X`.
* `freimanDimExponent_le` and `intFreimanDimExponent_le`: the exponents are at most
  `10 ^ 30 * κ ^ 7` and `10 ^ 32 * κ ^ 7` for `2 ≤ κ`.
-/

public section

open Finset SumOfSetsInSeveralDimensions
open scoped Pointwise

namespace ChangFreimanRuzsa

/-- The exponent `properizationExponent c + coordinateReductionExponent c + c` in the size bound of
Chang's theorem in `ZMod q` with the dimension bounded by the Freiman dimension, where `c` is
`containerExponent κ`. -/
@[expose] noncomputable def freimanDimExponent (κ : ℝ) : ℝ :=
  properizationExponent (containerExponent κ) + coordinateReductionExponent (containerExponent κ) +
    containerExponent κ

/-- The exponent `intExponent κ + coordinateReductionExponent (containerExponent (2 * κ))` in the
size bound of Chang's theorem for sets of integers with the dimension bounded by the Freiman
dimension. -/
@[expose] noncomputable def intFreimanDimExponent (κ : ℝ) : ℝ :=
  intExponent κ + coordinateReductionExponent (containerExponent (2 * κ))

/-- The second and third stages of Chang's theorem, in an abelian group in which the multiples
`n • a` with `n < N` of every nonzero `a` are distinct. Let `2 ≤ t`, write `c` for
`containerExponent κ`, `F` for `freimanDimExponent κ` and `T` for
`tProperExponent t (freimanDim X)`. Let a nonempty set `X` lie in a progression `P` of dimension at
most `c` and of size at most `exp c * #X`. If `exp (F + T) * #X ≤ N`, then `X` lies in a `t`-proper
progression of dimension at most `freimanDim X` and of size at most `exp (F + T) * #X`. -/
lemma exists_tProperGAP_dim_le_freimanDim_of_subset_gap {G : Type*} [DecidableEq G]
    [AddCommGroup G] {N t : ℕ} {κ : ℝ} {X : Finset G} {P : GAP G} (ht : 2 ≤ t)
    (hG : ∀ a : G, a ≠ 0 → Set.InjOn (fun n : ℕ ↦ n • a) (Set.Iio N)) (hX : X.Nonempty)
    (hXP : X ⊆ P.toFinset) (hPdim : P.dim ≤ containerExponent κ)
    (hPcard : #P.toFinset ≤ Real.exp (containerExponent κ) * #X)
    (hXN : Real.exp (freimanDimExponent κ + tProperExponent t (freimanDim X)) * #X ≤ N) :
    ∃ Q : GAP G, (t • Q).Proper ∧ X ⊆ Q.toFinset ∧ Q.dim ≤ freimanDim X ∧
      #Q.toFinset ≤ Real.exp (freimanDimExponent κ + tProperExponent t (freimanDim X)) * #X := by
  have hc : 0 ≤ containerExponent κ := (Nat.cast_nonneg _).trans hPdim
  have hF : Real.exp (freimanDimExponent κ) * #X ≤
      Real.exp (freimanDimExponent κ + tProperExponent t (freimanDim X)) * #X := by
    gcongr
    exact le_add_of_nonneg_right (tProperExponent_nonneg ht _)
  have hPX : Real.exp (properizationExponent P.dim + tProperExponent 2 P.dim) * #P.toFinset ≤
      Real.exp (freimanDimExponent κ) * #X := by
    rw [tProperExponent_two, add_zero, freimanDimExponent, Real.exp_add, mul_assoc]
    gcongr
    exact (properizationExponent_mono (Nat.cast_nonneg _) hPdim).trans
      (le_add_of_nonneg_right (coordinateReductionExponent_nonneg hc))
  obtain ⟨P₂, hP₂, hPP₂, hP₂dim, hP₂card⟩ :=
    exists_tProperGAP_toFinset_subset_dim_le_card_le_of_injOn_nsmul P le_rfl hG
      (hPX.trans (hF.trans hXN))
  rw [GAP.two_nsmul] at hP₂
  rw [tProperExponent_two, add_zero] at hP₂card
  have hP₂F : Real.exp (coordinateReductionExponent P₂.dim) * #P₂.toFinset ≤
      Real.exp (freimanDimExponent κ) * #X := by
    rw [freimanDimExponent, add_comm (properizationExponent _), add_assoc, Real.exp_add,
      Real.exp_add, mul_assoc, mul_assoc]
    gcongr
    · exact coordinateReductionExponent_mono (Nat.cast_nonneg _)
        ((Nat.cast_le.2 hP₂dim).trans hPdim)
    · refine hP₂card.trans ?_
      gcongr
      exact properizationExponent_mono (Nat.cast_nonneg _) hPdim
  have hP₂X : Real.exp (coordinateReductionExponent P₂.dim + tProperExponent t (freimanDim X)) *
      #P₂.toFinset ≤ Real.exp (freimanDimExponent κ + tProperExponent t (freimanDim X)) * #X := by
    rw [add_comm (coordinateReductionExponent _), add_comm (freimanDimExponent _), Real.exp_add,
      Real.exp_add, mul_assoc, mul_assoc]
    gcongr
  obtain ⟨Q, hQ, hXQ, hQdim, hQcard⟩ :=
    exists_tProperGAP_dim_le_freimanDim_of_injOn_nsmul ht hG hX hP₂ (hXP.trans hPP₂)
      (hP₂X.trans hXN)
  exact ⟨Q, hQ, hXQ, hQdim, hQcard.trans hP₂X⟩

/-- **Chang's theorem** in `ZMod q` for a prime `q`, with the dimension bounded by the Freiman
dimension. Let `2 ≤ t`, write `F` for `freimanDimExponent κ`, `T` for
`tProperExponent t (freimanDim X)` and `d` for `bohrGAPDim κ`. A set `X` with
`#(X + X) ≤ κ * #X`, `256 * d ≤ #X` and `exp (F + T) * #X ≤ q` is contained in a `t`-proper
generalized arithmetic progression of dimension at most `freimanDim X` and of size at most
`exp (F + T) * #X`. -/
theorem exists_tProperGAP_zmod_dim_le_freimanDim {q t : ℕ} {κ : ℝ} (X : Finset (ZMod q))
    (hq : q.Prime) (ht : 2 ≤ t) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X)
    (hXlower : 256 * (bohrGAPDim κ : ℝ) ≤ #X)
    (hXupper : Real.exp (freimanDimExponent κ + tProperExponent t (freimanDim X)) * #X ≤ q) :
    ∃ Q : GAP (ZMod q), (t • Q).Proper ∧ X ⊆ Q.toFinset ∧ Q.dim ≤ freimanDim X ∧
      #Q.toFinset ≤ Real.exp (freimanDimExponent κ + tProperExponent t (freimanDim X)) * #X := by
  obtain ⟨P, hXP, hPdim, hPcard⟩ := exists_gap_zmod_subset_dim_le_card_le X hq hκ hXX hXlower
  exact exists_tProperGAP_dim_le_freimanDim_of_subset_gap ht
    (fun _ ↦ GAP.injOn_nsmul_of_prime hq) (nonempty_of_mul_bohrGAPDim_le hXlower) hXP hPdim
    hPcard hXupper

/-- **Chang's theorem** for sets of integers, with the dimension bounded by the Freiman dimension.
Let `2 ≤ t`, write `E` for `intFreimanDimExponent κ` and `T` for
`tProperExponent t (freimanDim X)`. A finite nonempty set `X : Finset ℤ` with
`#(X + X) ≤ κ * #X` is contained in a `t`-proper generalized arithmetic progression of dimension
at most `freimanDim X` and of size at most `exp (E + T) * #X`. -/
theorem exists_tProperGAP_int_dim_le_freimanDim {t : ℕ} {κ : ℝ} (X : Finset ℤ) (hX : X.Nonempty)
    (ht : 2 ≤ t) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X) :
    ∃ Q : GAP ℤ, (t • Q).Proper ∧ X ⊆ Q.toFinset ∧ Q.dim ≤ freimanDim X ∧
      #Q.toFinset ≤ Real.exp (intFreimanDimExponent κ + tProperExponent t (freimanDim X)) * #X := by
  obtain ⟨P, hP, hXP, hPdim, hPcard⟩ := exists_tProperGAP_of_small_sumset X hX le_rfl hκ hXX
  rw [GAP.two_nsmul] at hP
  rw [tProperExponent_two, add_zero] at hPcard
  obtain ⟨Q, hQ, hXQ, hQdim, hQcard⟩ :=
    exists_tProperGAP_dim_le_freimanDim_of_isAddTorsionFree ht hX hP hXP
  refine ⟨Q, hQ, hXQ, hQdim, hQcard.trans ?_⟩
  rw [intFreimanDimExponent, add_comm (intExponent κ), add_right_comm,
    Real.exp_add _ (intExponent κ), mul_assoc]
  gcongr
  exact coordinateReductionExponent_mono (Nat.cast_nonneg _) hPdim

/-- `freimanDimExponent κ` is at most `10 ^ 30 * κ ^ 7` for `2 ≤ κ`. -/
lemma freimanDimExponent_le {κ : ℝ} (hκ : 2 ≤ κ) : freimanDimExponent κ ≤ 10 ^ 30 * κ ^ 7 := by
  have h := containerExponent_add_two_pow_mul_log_le hκ
  unfold freimanDimExponent properizationExponent coordinateReductionExponent
  rw [mul_assoc 2, mul_assoc 4]
  linarith [containerExponent_le hκ, one_le_pow₀ (n := 7) (by linarith : (1 : ℝ) ≤ κ),
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ κ) (by norm_num : 3 ≤ 7)]

/-- `intFreimanDimExponent κ` is at most `10 ^ 32 * κ ^ 7` for `2 ≤ κ`. -/
lemma intFreimanDimExponent_le {κ : ℝ} (hκ : 2 ≤ κ) :
    intFreimanDimExponent κ ≤ 10 ^ 32 * κ ^ 7 := by
  have h := containerExponent_add_two_pow_mul_log_le (κ := 2 * κ) (by linarith)
  rw [mul_pow] at h
  unfold intFreimanDimExponent coordinateReductionExponent
  rw [mul_assoc 4]
  linarith [intExponent_le hκ, one_le_pow₀ (n := 7) (by linarith : (1 : ℝ) ≤ κ)]

end ChangFreimanRuzsa
