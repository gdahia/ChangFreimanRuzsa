/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

import APAP.Mathlib.Analysis.Normed.Ring.Basic
import APAP.Prereqs.Convolution.Discrete.Basic
import AddCombi.Mathlib.Algebra.BigOperators.Ring.Finset
import AddCombi.Mathlib.Algebra.GroupWithZero.Indicator
import Mathlib.Algebra.Order.Chebyshev

public import APAPCompat.Prereqs.Chang
public import AddCombi.Mathlib.Algebra.Notation.Indicator
import APAP.Prereqs.LpNorm.Discrete.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Fourier analysis for Chang's theorem

Let $X \subseteq \mathbb{Z}/q\mathbb{Z}$ satisfy $|X + X| \le \kappa |X|$ with $\kappa \ge 2$.

## Main statements

* `fourthEnergy_lower_bound`: $|X|^3 \le \kappa E(X)$, where $E(X)$ is the additive energy.
* `changLargeSpectrum_chord_subset_fourfold`: the set of $x$ with $|1 - \psi(x)| \le 1/4$ for every
  $\psi$ in the large spectrum of $1_X$ at threshold $\eta = (8\kappa)^{-1/2}$ lies in
  $2X - 2X$.
* `exists_changLargeSpectrum_generators`: Chang's lemma, which puts the large spectrum in the span
  of a small set $\Delta$ of characters.
* `changGenerators_chord_subset_fourfold`: the same inclusion with the large spectrum replaced by
  $\Delta$ and the chord width $1/4$ by $(4(|\Delta| + 1))^{-1}$.
* `exists_frequency_chord_le`: $|1 - \psi_r(x)| \le 2\pi |a| / q$ for every integer $a$ with
  $a \equiv r x \pmod q$.

The discrete Fourier transform, large spectra and Chang's lemma come from the APAP library.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open Finset Fintype MeasureTheory RCLike
open scoped BigOperators ComplexConjugate Indicator NNReal Pointwise

noncomputable section

/-! ## Fourth energy -/

private def changIndicatorReal {G : Type*} (X : Finset G) : G → ℝ :=
  𝟭_[(X : Set G)]

private def changPairCount {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (X : Finset G) : G → ℝ :=
  changIndicatorReal X ∗ᵈ^ 2

private lemma changPairCount_eq_zero_of_not_mem_add
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {X : Finset G} {a : G} (ha : a ∉ X + X) :
    changPairCount X a = 0 := by
  rw [changPairCount, changIndicatorReal, indicator_one_iterConv_apply]
  norm_cast
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx hsum
  apply ha
  rw [Finset.mem_add]
  refine ⟨x 0, Fintype.mem_piFinset.mp hx 0, x 1, Fintype.mem_piFinset.mp hx 1, ?_⟩
  simpa [Fin.sum_univ_two] using hsum

private lemma sum_changPairCount
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (X : Finset G) :
    ∑ a, changPairCount X a = (X.card : ℝ) ^ 2 := by
  rw [changPairCount, sum_iterConv]
  congr 1
  simp [changIndicatorReal]

private lemma sum_changPairCount_add
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (X : Finset G) :
    ∑ a ∈ X + X, changPairCount X a = (X.card : ℝ) ^ 2 := by
  rw [← sum_changPairCount]
  apply Fintype.sum_subset
  intro a ha
  by_contra hmem
  exact ha (changPairCount_eq_zero_of_not_mem_add hmem)

private lemma boringEnergy_two_eq_sum_changPairCount_sq
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (X : Finset G) :
    boringEnergy 2 X = ∑ a, changPairCount X a ^ 2 := by
  rw [boringEnergy_eq]
  rfl

/-- If $|X + X| \le \kappa |X|$, then $|X|^3 \le \kappa E(X)$, where $E(X)$ = `boringEnergy 2 X`
is the number of additive quadruples in $X$. -/
lemma fourthEnergy_lower_bound {q : ℕ} [NeZero q] {κ : ℝ} (X : Finset (ZMod q))
    (hX : X.Nonempty) (hXX : ((X + X).card : ℝ) ≤ κ * X.card) :
    (X.card : ℝ) ^ 3 ≤ κ * boringEnergy 2 X := by
  have hcauchy :
      ((X.card : ℝ) ^ 2) ^ 2 ≤ ((X + X).card : ℝ) * boringEnergy 2 X := by
    rw [boringEnergy_two_eq_sum_changPairCount_sq, ← sum_changPairCount_add]
    apply (sq_sum_le_card_mul_sum_sq
      (s := X + X) (f := changPairCount X)).trans_eq
    congr 1
    apply Fintype.sum_subset
    intro a ha
    by_contra hmem
    apply ha
    simp [changPairCount_eq_zero_of_not_mem_add hmem]
  nlinarith [sq_nonneg ((X.card : ℝ) ^ 2 - κ * boringEnergy 2 X),
    hcauchy.trans (mul_le_mul_of_nonneg_right hXX (energy_nonneg 2 X trivChar)),
    (by exact_mod_cast hX.card_pos : (0 : ℝ) < X.card)]

/-! ## Large spectrum -/

/-- The indicator function of `X`, with complex values. -/
def changIndicatorComplex {G : Type*} (X : Finset G) : G → ℂ :=
  𝟭_[(X : Set G)]

private def changFourfoldCorrelation
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (X : Finset G) : G → ℂ :=
  (changIndicatorComplex X ∗ᵈ^ 2) ○ᵈ (changIndicatorComplex X ∗ᵈ^ 2)

private lemma dft_changFourfoldCorrelation
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (X : Finset G) (ψ : AddChar G ℂ) :
    dft (changFourfoldCorrelation X) ψ =
      (‖dft (changIndicatorComplex X) ψ‖ ^ 4 : ℝ) := by
  rw [changFourfoldCorrelation, dft_dddconv_apply, dft_iterConv, Pi.pow_apply, map_pow,
    ← mul_pow, Complex.mul_conj']
  push_cast
  ring

private lemma expect_fourier_changFourfoldCorrelation
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (X : Finset G) (x : G) :
    𝔼 ψ, ((‖dft (changIndicatorComplex X) ψ‖ ^ 4 : ℝ) : ℂ) * ψ x =
      changFourfoldCorrelation X x := by
  rw [← dft_inversion (changFourfoldCorrelation X) x]
  congr! 3 with ψ
  rw [dft_changFourfoldCorrelation]

private lemma fourthMoment_changIndicatorComplex
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (X : Finset G) :
    𝔼 ψ, ‖dft (changIndicatorComplex X) ψ‖ ^ 4 = boringEnergy 2 X := by
  let : MeasurableSpace G := ⊤
  rw [← cLpNorm_pow_eq_expect_norm (by norm_num)
    (dft (changIndicatorComplex X)), changIndicatorComplex]
  simpa using cLpNorm_dft_indicator_one_pow 2 X

private lemma secondMoment_changIndicatorComplex
    {G : Type*} [AddCommGroup G] [Fintype G]
    (X : Finset G) :
    𝔼 ψ, ‖dft (changIndicatorComplex X) ψ‖ ^ 2 = X.card := by
  classical
  let : MeasurableSpace G := ⊤
  rw [← cLpNorm_pow_eq_expect_norm (by norm_num)
    (dft (changIndicatorComplex X)), changIndicatorComplex]
  convert cLpNorm_dft_indicator_one_pow 1 X using 1
  all_goals norm_num

private lemma changFourfoldCorrelation_ne_zero_mem_sub
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (X : Finset G) {x : G} (hx : changFourfoldCorrelation X x ≠ 0) :
    x ∈ (X + X) - (X + X) := by
  have hsupport :
      Function.support (changIndicatorComplex X ∗ᵈ^ 2) ⊆
        ((X + X : Finset G) : Set G) := by
    apply (support_iterConv_subset (changIndicatorComplex X) 2).trans
    rw [changIndicatorComplex, Set.support_indicator_one]
    intro y hy
    simpa [two_nsmul] using hy
  apply Finset.mem_coe.mp
  change x ∈ Function.support (changFourfoldCorrelation X) at hx
  apply Set.mem_of_mem_of_subset hx
  rw [changFourfoldCorrelation]
  simpa using (support_dddconv_subset _ _).trans (Set.sub_subset_sub hsupport hsupport)

/-- The large spectrum of the indicator of `X` at threshold $\eta$: the characters $\psi$ with
$|\hat{1}_X(\psi)| \ge \eta |X|$. -/
def changLargeSpectrum {q : ℕ} [NeZero q] (X : Finset (ZMod q)) (η : ℝ) :
    Finset (AddChar (ZMod q) ℂ) :=
  largeSpec (changIndicatorComplex X) η

private lemma weighted_chord_error_le
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    (X : Finset G) {η ε : ℝ} (hε : 0 ≤ ε) (x : G)
    (hx : ∀ ψ ∈ largeSpec (changIndicatorComplex X) η, ‖1 - ψ x‖ ≤ ε) :
    (𝔼 ψ, ‖dft (changIndicatorComplex X) ψ‖ ^ 4 * ‖1 - ψ x‖) ≤
      ε * boringEnergy 2 X + 2 * (η * X.card) ^ 2 * X.card := by
  refine (Finset.expect_le_expect
    (g := fun ψ ↦ ε * ‖dft (changIndicatorComplex X) ψ‖ ^ 4 +
      2 * (η * X.card) ^ 2 * ‖dft (changIndicatorComplex X) ψ‖ ^ 2)
    ?_).trans_eq ?_
  · intro ψ _
    by_cases hψ : ψ ∈ largeSpec (changIndicatorComplex X) η
    · refine (mul_le_mul_of_nonneg_left (hx ψ hψ)
        (pow_nonneg (norm_nonneg _) 4)).trans ?_
      rw [mul_comm (‖dft (changIndicatorComplex X) ψ‖ ^ 4) ε]
      exact le_add_of_nonneg_right (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg (η * X.card)))
        (sq_nonneg ‖dft (changIndicatorComplex X) ψ‖))
    · have hhat :
          ‖dft (changIndicatorComplex X) ψ‖ < η * X.card := by
        rw [largeSpec, Finset.mem_filter, not_and_or, not_le] at hψ
        simpa [changIndicatorComplex] using
          hψ.resolve_left fun h ↦ h (Finset.mem_univ ψ)
      have hhat_sq : ‖dft (changIndicatorComplex X) ψ‖ ^ 2 ≤ (η * X.card) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hhat.le 2
      have hchord : ‖1 - ψ x‖ ≤ 2 :=
        (norm_sub_le _ _).trans_eq (by norm_num [AddChar.norm_apply])
      apply (mul_le_mul_of_nonneg_left hchord
        (pow_nonneg (norm_nonneg _) 4)).trans
      nlinarith [mul_le_mul_of_nonneg_left hhat_sq
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
          (sq_nonneg ‖dft (changIndicatorComplex X) ψ‖)),
        mul_nonneg hε
          (pow_nonneg (norm_nonneg (dft (changIndicatorComplex X) ψ)) 4)]
  · rw [Finset.expect_add_distrib, ← Finset.mul_expect, ← Finset.mul_expect,
      fourthMoment_changIndicatorComplex, secondMoment_changIndicatorComplex]

private lemma spectrum_chord_subset_fourfold
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    (X : Finset G) {η ε : ℝ} (hε : 0 ≤ ε)
    (hbudget : ε * boringEnergy 2 X + 2 * (η * X.card) ^ 2 * X.card <
      boringEnergy 2 X) :
    {x | ∀ ψ ∈ largeSpec (changIndicatorComplex X) η, ‖1 - ψ x‖ ≤ ε} ⊆
      ((X + X) - (X + X) : Finset G) := by
  intro x hx
  apply changFourfoldCorrelation_ne_zero_mem_sub X
  intro hzero
  have herr :
      ((boringEnergy 2 X : ℝ) : ℂ) =
        𝔼 ψ, ((‖dft (changIndicatorComplex X) ψ‖ ^ 4 : ℝ) : ℂ) *
          (1 - ψ x) := by
    simp_rw [mul_sub, mul_one]
    rw [Finset.expect_sub_distrib, expect_fourier_changFourfoldCorrelation, hzero, sub_zero,
      ← fourthMoment_changIndicatorComplex X]
    norm_cast
  have hnorm := norm_expect_le (K := ℝ) (s := Finset.univ)
    (f := fun ψ : AddChar G ℂ ↦ ((‖dft (changIndicatorComplex X) ψ‖ ^ 4 : ℝ) : ℂ) * (1 - ψ x))
  rw [← herr, Complex.norm_real,
    Real.norm_of_nonneg (by exact energy_nonneg 2 X trivChar : 0 ≤ boringEnergy 2 X)] at hnorm
  refine not_le_of_gt ((weighted_chord_error_le X hε x hx).trans_lt hbudget) ?_
  simpa [norm_mul] using hnorm

/-- At the threshold $\eta = (8\kappa)^{-1/2}$, the set of $x$ with $|1 - \psi(x)| \le 1/4$ for
every $\psi$ in the large spectrum lies in $2X - 2X$. -/
lemma changLargeSpectrum_chord_subset_fourfold
    {q : ℕ} [NeZero q] {κ : ℝ}
    (X : Finset (ZMod q)) (hκ : 2 ≤ κ) (hX : X.Nonempty)
    (hXX : ((X + X).card : ℝ) ≤ κ * X.card) :
    {x | ∀ ψ ∈ changLargeSpectrum X (Real.sqrt ((8 * κ)⁻¹)),
      ‖1 - ψ x‖ ≤ (1 : ℝ) / 4} ⊆
      ((X + X) - (X + X) : Finset (ZMod q)) := by
  let : MeasurableSpace (ZMod q) := ⊤
  apply spectrum_chord_subset_fourfold X (by norm_num)
  have hκpos : 0 < κ := by linarith
  have henergy := fourthEnergy_lower_bound X hX hXX
  have hXpos : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have henergypos : 0 < boringEnergy 2 X := by
    by_contra! hnonpos
    nlinarith [pow_pos hXpos 3, mul_nonpos_of_nonneg_of_nonpos hκpos.le hnonpos]
  rw [mul_pow, Real.sq_sqrt (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ 8 * κ))]
  nlinarith [mul_nonneg (sq_nonneg (X.card : ℝ)) hXpos.le,
    mul_nonneg hκpos.le henergypos.le, mul_inv_cancel₀ (by positivity : 8 * κ ≠ 0)]

private lemma changIndicatorComplex_ne_zero
    {G : Type*} {X : Finset G} (hX : X.Nonempty) :
    changIndicatorComplex X ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ := hX
  intro hzero
  simpa [changIndicatorComplex, hx] using congrFun hzero x

private lemma changIndicator_density_parameter
    {G : Type*} [AddCommGroup G] [Fintype G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G] (X : Finset G) :
    ‖changIndicatorComplex X‖_[1] ^ 2 / ‖changIndicatorComplex X‖_[2] ^ 2 /
      Fintype.card G = (X.card : ℝ) / Fintype.card G := by
  rw [changIndicatorComplex, dL1Norm_indicator_one, dL2Norm_indicator_one,
    Real.sq_sqrt (Nat.cast_nonneg X.card)]
  field_simp

/-- **Chang's lemma.** The large spectrum of $1_X$ at threshold $\eta$ lies in the span of a
subset $\Delta$ of itself with
$|\Delta| \le \lceil C e \lceil 1 + \log(q / |X|) \rceil / \eta^2 \rceil$, where $C$ is
`changConst`. -/
lemma exists_changLargeSpectrum_generators {q : ℕ} [NeZero q]
    (X : Finset (ZMod q)) (hX : X.Nonempty) {η : ℝ} (hη : 0 < η) :
    ∃ Δ, Δ ⊆ changLargeSpectrum X η ∧
      Δ.card ≤
        ⌈changConst * Real.exp 1 *
          ⌈1 + Real.log (((X.card : ℝ) / q)⁻¹)⌉₊ / η ^ 2⌉₊ ∧
      changLargeSpectrum X η ⊆ Δ.addSpan := by
  let : MeasurableSpace (ZMod q) := ⊤
  convert chang (changIndicatorComplex_ne_zero hX) hη using 1
  rw [changIndicator_density_parameter, ZMod.card]
  rfl

private lemma norm_one_sub_zpow_le {z : ℂ} (hz : ‖z‖ = 1) {e : ℤ}
    (he : e = -1 ∨ e = 0 ∨ e = 1) :
    ‖1 - z ^ e‖ ≤ ‖1 - z‖ := by
  rcases he with rfl | rfl | rfl
  · rw [zpow_neg_one, Complex.inv_eq_conj hz]
    apply le_of_eq
    simpa using RCLike.norm_conj (1 - z)
  · simp
  · rw [zpow_one]

private lemma norm_one_sub_prod_le_sum {ι : Type*}
    {s : Finset ι} {f : ι → ℂ} (hf : ∀ i ∈ s, ‖f i‖ = 1) :
    ‖1 - ∏ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖1 - f i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [prod_insert ha, sum_insert ha]
      exact (norm_one_sub_mul (c := 1) (hf a (mem_insert_self a s)).le).trans
        (add_le_add le_rfl (ih fun i hi ↦ hf i (mem_insert_of_mem hi)))

private lemma norm_one_sub_addSpan_apply_le
    {G : Type*} [AddCommGroup G] [Finite G]
    {Δ : Finset (AddChar G ℂ)} {ψ : AddChar G ℂ}
    (hψ : ψ ∈ Δ.addSpan) (x : G) :
    ‖1 - ψ x‖ ≤ ∑ γ ∈ Δ, ‖1 - γ x‖ := by
  obtain ⟨e, he, hsum⟩ := Finset.mem_addSpan.1 hψ
  rw [← hsum, AddChar.sum_apply]
  simp_rw [AddChar.zsmul_apply]
  refine (norm_one_sub_prod_le_sum ?_).trans ?_
  · intro γ hγ
    rw [norm_zpow, AddChar.norm_apply, one_zpow]
  · apply Finset.sum_le_sum
    intro γ hγ
    exact norm_one_sub_zpow_le (AddChar.norm_apply γ x) (he γ)

/-- If the large spectrum at threshold $(8\kappa)^{-1/2}$ lies in the span of $\Delta$, then the
set of $x$ with $|1 - \psi(x)| \le (4(|\Delta| + 1))^{-1}$ for every $\psi \in \Delta$ lies in
$2X - 2X$. -/
lemma changGenerators_chord_subset_fourfold
    {q : ℕ} [NeZero q] {κ : ℝ}
    (X : Finset (ZMod q)) (hκ : 2 ≤ κ) (hX : X.Nonempty)
    (hXX : ((X + X).card : ℝ) ≤ κ * X.card)
    {Δ : Finset (AddChar (ZMod q) ℂ)}
    (hspan : changLargeSpectrum X (Real.sqrt ((8 * κ)⁻¹)) ⊆ Δ.addSpan) :
    {x | ∀ ψ ∈ Δ, ‖1 - ψ x‖ ≤
      ((4 : ℝ) * (Δ.card + 1))⁻¹} ⊆
      ((X + X) - (X + X) : Finset (ZMod q)) := by
  intro x hx
  apply changLargeSpectrum_chord_subset_fourfold X hκ hX hXX
  intro ψ hψ
  apply (norm_one_sub_addSpan_apply_le (hspan hψ) x).trans
  apply (Finset.sum_le_sum hx).trans
  rw [sum_const, nsmul_eq_mul, inv_eq_one_div, mul_one_div]
  apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
  nlinarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ Δ.card)]

/-! ## Frequencies

Chord widths are the analytic form of the Bohr condition. The construction of a progression inside
a chord neighborhood works instead with integer representatives $a$ of the products $r x$ of
frequencies with group elements, together with bounds on $|a|$. -/

/-- Every character $\psi$ of $\mathbb{Z}/q\mathbb{Z}$ is given by a frequency $r$, and
$|1 - \psi(x)| \le 2 \pi |a| / q$ for every integer $a$ with $a \equiv r x \pmod q$. -/
lemma exists_frequency_chord_le {q : ℕ} [NeZero q] (ψ : AddChar (ZMod q) ℂ) :
    ∃ r : ZMod q, ∀ (x : ZMod q) (a : ℤ), ((a : ZMod q) = r * x) →
      ‖1 - ψ x‖ ≤ 2 * Real.pi * |(a : ℝ)| / q := by
  obtain ⟨r, rfl⟩ := AddChar.zmodAddEquiv.surjective ψ
  use r
  intro x a ha
  have hψ : (AddChar.zmodAddEquiv r) x = ZMod.stdAddChar ((a : ZMod q)) := by
    rw [ha]
    rfl
  rw [hψ, ZMod.stdAddChar_coe, norm_sub_rev]
  refine le_trans (le_of_eq ?_)
    ((Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * a / q)).trans (le_of_eq ?_))
  · congr 3
    push_cast
    ring
  · rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
      Nat.abs_cast]

end

end ChangFreimanRuzsa
