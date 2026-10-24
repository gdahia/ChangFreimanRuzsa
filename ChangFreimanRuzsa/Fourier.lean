/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import APAP.Prereqs.Chang
public import Mathlib.Combinatorics.Additive.Energy
import APAP.Mathlib.Analysis.Normed.Ring.Basic
import APAP.Prereqs.Convolution.Discrete.Basic
import APAP.Prereqs.LpNorm.Discrete.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Fourier analysis for Chang's theorem

Let `X` be a finite subset of a finite abelian group with `#(X + X) ≤ κ * #X` and `2 ≤ κ`.

## Main statements

* `card_pow_three_le_mul_addEnergy`: `#X ^ 3 ≤ κ * E[X]`, where `E[X]` is the additive energy.
* `mem_add_sub_add_of_card_add_le_of_forall_largeSpec`: every `x` with `‖1 - ψ x‖ ≤ 4⁻¹` for
  every `ψ` in the large spectrum of `𝟭_[X]` at threshold `η = √(8 * κ)⁻¹` lies in
  `X + X - (X + X)`.
* `exists_card_le_largeSpec_subset_addSpan`: Chang's lemma in `ZMod q`, which puts the large
  spectrum in the span of a small set `Δ` of characters.
* `mem_add_sub_add_of_largeSpec_subset_addSpan`: the same inclusion with the large spectrum replaced
  by `Δ` and the width `4⁻¹` by `(4 * (#Δ + 1))⁻¹`.
* `exists_frequency_chord_le`: every character `ψ` of `ZMod q` has a frequency `r` such that
  `‖1 - ψ x‖ ≤ 2 * π * |a| / q` for every integer `a` with `(a : ZMod q) = r * x`.

The discrete Fourier transform, large spectra and Chang's lemma come from the APAP library, and the
additive energy from Mathlib.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open Finset Fintype MeasureTheory RCLike
open scoped BigOperators Combinatorics.Additive ComplexConjugate NNReal Pointwise

/-- The indicator function `𝟭_[s, R]` of a set `s`, with values `0` and `1` in `R`. -/
local notation3 "𝟭_[" s ", " R "]" => Set.indicator s fun _ ↦ (1 : R)

/-- The indicator function `𝟭_[s]` of a set `s`, with values in a type given by the context. -/
local notation3 "𝟭_[" s "]" => 𝟭_[s, _]

noncomputable section

variable {G : Type*} [AddCommGroup G]

/-! ## Additive energy -/

section Energy

variable [DecidableEq G]

/-- The fourth moment `boringEnergy 2 s` of APAP is the additive energy `E[s]`. -/
lemma boringEnergy_two_eq_addEnergy [Finite G] (s : Finset G) : boringEnergy 2 s = E[s] := by
  cases nonempty_fintype G
  rw [boringEnergy_eq, addEnergy_eq_sum_sq]
  push_cast
  congr with x
  rw [iterConv_succ, iterConv_one, indicator_one_ddconv_indicator_one_eq_sum]

/-- If `X` is nonempty and `#(X + X) ≤ κ * #X`, then `#X ^ 3 ≤ κ * E[X]`. -/
lemma card_pow_three_le_mul_addEnergy {X : Finset G} {κ : ℝ} (hX : X.Nonempty)
    (hXX : #(X + X) ≤ κ * #X) : #X ^ 3 ≤ κ * E[X] := by
  have hX₀ : (0 : ℝ) < #X := by exact_mod_cast hX.card_pos
  nlinarith [(by exact_mod_cast le_card_add_mul_addEnergy X X :
      (#X : ℝ) ^ 2 * #X ^ 2 ≤ #(X + X) * E[X]),
    mul_le_mul_of_nonneg_right hXX (Nat.cast_nonneg (α := ℝ) E[X])]

end Energy

/-! ## Characters in a span -/

section Span

private lemma norm_one_sub_zpow_le {z : ℂ} (hz : ‖z‖ = 1) {e : ℤ}
    (he : e = -1 ∨ e = 0 ∨ e = 1) : ‖1 - z ^ e‖ ≤ ‖1 - z‖ := by
  rcases he with rfl | rfl | rfl
  · rw [zpow_neg_one, Complex.inv_eq_conj hz]
    simpa using (RCLike.norm_conj (1 - z)).le
  · simp
  · rw [zpow_one]

private lemma norm_one_sub_prod_le_sum {ι : Type*} {s : Finset ι} {f : ι → ℂ}
    (hf : ∀ i ∈ s, ‖f i‖ = 1) : ‖1 - ∏ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖1 - f i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    apply (norm_one_sub_mul (c := 1) (hf a (mem_insert_self a s)).le).trans
    gcongr
    apply ih
    intro i hi
    exact hf i (mem_insert_of_mem hi)

variable [Finite G]

/-- If `ψ` lies in the span of `Δ`, then `‖1 - ψ x‖ ≤ ∑ γ ∈ Δ, ‖1 - γ x‖`. -/
lemma norm_one_sub_apply_le_sum_of_mem_addSpan {Δ : Finset (AddChar G ℂ)} {ψ : AddChar G ℂ}
    (hψ : ψ ∈ Δ.addSpan) (x : G) : ‖1 - ψ x‖ ≤ ∑ γ ∈ Δ, ‖1 - γ x‖ := by
  obtain ⟨e, he, rfl⟩ := mem_addSpan.1 hψ
  rw [AddChar.sum_apply]
  simp_rw [AddChar.zsmul_apply]
  refine (norm_one_sub_prod_le_sum ?_).trans ?_
  · intro γ _
    rw [norm_zpow, AddChar.norm_apply, one_zpow]
  · apply sum_le_sum
    intro γ _
    exact norm_one_sub_zpow_le (AddChar.norm_apply γ x) (he γ)

end Span

/-! ## Large spectrum -/

section LargeSpec

variable [DecidableEq G] [Fintype G]

/-- Fourier inversion for the function `(𝟭_[X] ∗ᵈ^ 2) ○ᵈ (𝟭_[X] ∗ᵈ^ 2)`, whose Fourier transform
is `‖dft 𝟭_[X] ψ‖ ^ 4`. -/
private lemma expect_norm_dft_pow_four_mul_apply (X : Finset G) (x : G) :
    𝔼 ψ, (‖dft 𝟭_[(X : Set G), ℂ] ψ‖ : ℂ) ^ 4 * ψ x =
      ((𝟭_[(X : Set G), ℂ] ∗ᵈ^ 2) ○ᵈ (𝟭_[(X : Set G)] ∗ᵈ^ 2)) x := by
  rw [← dft_inversion ((𝟭_[(X : Set G), ℂ] ∗ᵈ^ 2) ○ᵈ (𝟭_[(X : Set G)] ∗ᵈ^ 2)) x]
  congr with ψ
  rw [dft_dddconv_apply, dft_iterConv, Pi.pow_apply, map_pow, ← mul_pow, Complex.mul_conj']
  ring

/-- The function `(𝟭_[X] ∗ᵈ^ 2) ○ᵈ (𝟭_[X] ∗ᵈ^ 2)` vanishes outside `X + X - (X + X)`. -/
private lemma iterConv_two_dddconv_apply_eq_zero {X : Finset G} {x : G}
    (hx : x ∉ (X + X) - (X + X)) :
    ((𝟭_[(X : Set G), ℂ] ∗ᵈ^ 2) ○ᵈ (𝟭_[(X : Set G)] ∗ᵈ^ 2)) x = 0 := by
  have h := support_iterConv_subset 𝟭_[(X : Set G), ℂ] 2
  rw [Set.support_indicator, Function.support_const one_ne_zero, Set.inter_univ, two_nsmul] at h
  apply Function.notMem_support.1
  intro hmem
  apply hx
  rw [← mem_coe, coe_sub, coe_add]
  exact Set.sub_subset_sub h h (support_dddconv_subset _ _ hmem)

variable [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- The fourth moment of `dft 𝟭_[X]` is the additive energy of `X`. -/
lemma expect_norm_dft_indicator_pow_four (X : Finset G) :
    𝔼 ψ, ‖dft 𝟭_[(X : Set G), ℂ] ψ‖ ^ 4 = E[X] := by
  rw [← boringEnergy_two_eq_addEnergy, ← cLpNorm_pow_eq_expect_norm (by norm_num)]
  simpa using cLpNorm_dft_indicator_one_pow 2 X

omit [DecidableEq G] in
/-- The second moment of `dft 𝟭_[X]` is `#X`. -/
lemma expect_norm_dft_indicator_sq (X : Finset G) :
    𝔼 ψ, ‖dft 𝟭_[(X : Set G), ℂ] ψ‖ ^ 2 = #X := by
  rw [← cLpNorm_pow_eq_expect_norm (by norm_num)]
  simp

/-- If `x ∉ X + X - (X + X)`, then `E[X] ≤ 𝔼 ψ, ‖dft 𝟭_[X] ψ‖ ^ 4 * ‖1 - ψ x‖`. -/
private lemma addEnergy_le_expect_norm_dft_pow_four_mul {X : Finset G} {x : G}
    (hx : x ∉ (X + X) - (X + X)) :
    (E[X] : ℝ) ≤ 𝔼 ψ, ‖dft 𝟭_[(X : Set G), ℂ] ψ‖ ^ 4 * ‖1 - ψ x‖ := by
  have h : (E[X] : ℂ) = 𝔼 ψ, (‖dft 𝟭_[(X : Set G), ℂ] ψ‖ : ℂ) ^ 4 * (1 - ψ x) := by
    simp_rw [mul_sub, mul_one]
    rw [expect_sub_distrib, expect_norm_dft_pow_four_mul_apply,
      iterConv_two_dddconv_apply_eq_zero hx, sub_zero]
    exact_mod_cast (expect_norm_dft_indicator_pow_four X).symm
  rw [← Complex.norm_natCast E[X], h]
  refine (norm_expect_le (K := ℝ)).trans_eq ?_
  simp

/-- If `‖1 - ψ x‖ ≤ ε` on the large spectrum at threshold `η`, then
`𝔼 ψ, ‖dft 𝟭_[X] ψ‖ ^ 4 * ‖1 - ψ x‖ ≤ ε * E[X] + 2 * η ^ 2 * #X ^ 3`. -/
private lemma expect_norm_dft_pow_four_mul_le {X : Finset G} {η ε : ℝ} (hε : 0 ≤ ε) {x : G}
    (hx : ∀ ψ ∈ largeSpec 𝟭_[(X : Set G)] η, ‖1 - ψ x‖ ≤ ε) :
    𝔼 ψ, ‖dft 𝟭_[(X : Set G), ℂ] ψ‖ ^ 4 * ‖1 - ψ x‖ ≤ ε * E[X] + 2 * (η * #X) ^ 2 * #X := by
  trans 𝔼 ψ, (ε * ‖dft 𝟭_[(X : Set G), ℂ] ψ‖ ^ 4 +
    2 * (η * #X) ^ 2 * ‖dft 𝟭_[(X : Set G), ℂ] ψ‖ ^ 2)
  · apply expect_le_expect
    intro ψ _
    by_cases hψ : ψ ∈ largeSpec 𝟭_[(X : Set G)] η
    · nlinarith [mul_le_mul_of_nonneg_left (hx ψ hψ)
          (by positivity : 0 ≤ ‖dft 𝟭_[(X : Set G), ℂ] ψ‖ ^ 4),
        (by positivity : 0 ≤ 2 * (η * #X) ^ 2 * ‖dft 𝟭_[(X : Set G), ℂ] ψ‖ ^ 2)]
    · nlinarith [mul_le_mul_of_nonneg_left
          ((norm_sub_le _ _).trans_eq (by norm_num [AddChar.norm_apply]) : ‖1 - ψ x‖ ≤ 2)
          (by positivity : 0 ≤ ‖dft 𝟭_[(X : Set G), ℂ] ψ‖ ^ 4),
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _)
          (by simpa using hψ : ‖dft 𝟭_[(X : Set G), ℂ] ψ‖ < η * #X).le 2)
          (by positivity : 0 ≤ 2 * ‖dft 𝟭_[(X : Set G), ℂ] ψ‖ ^ 2),
        mul_nonneg hε (by positivity : 0 ≤ ‖dft 𝟭_[(X : Set G), ℂ] ψ‖ ^ 4)]
  · rw [expect_add_distrib, ← mul_expect, ← mul_expect, expect_norm_dft_indicator_pow_four,
      expect_norm_dft_indicator_sq]

/-- Let `‖1 - ψ x‖ ≤ ε` for every `ψ` in the large spectrum of `𝟭_[X]` at threshold `η`. If
`ε * E[X] + 2 * η ^ 2 * #X ^ 3 < E[X]`, then `x ∈ X + X - (X + X)`. -/
lemma mem_add_sub_add_of_forall_largeSpec_norm_one_sub_le {X : Finset G} {η ε : ℝ} (hε : 0 ≤ ε)
    (hεη : ε * E[X] + 2 * (η * #X) ^ 2 * #X < E[X]) {x : G}
    (hx : ∀ ψ ∈ largeSpec 𝟭_[(X : Set G)] η, ‖1 - ψ x‖ ≤ ε) : x ∈ (X + X) - (X + X) := by
  by_contra hmem
  exact ((expect_norm_dft_pow_four_mul_le hε hx).trans_lt hεη).not_ge
    (addEnergy_le_expect_norm_dft_pow_four_mul hmem)

/-- If `#(X + X) ≤ κ * #X` with `2 ≤ κ`, every `x` with `‖1 - ψ x‖ ≤ 4⁻¹` for every `ψ` in the
large spectrum of `𝟭_[X]` at threshold `√(8 * κ)⁻¹` lies in `X + X - (X + X)`. -/
lemma mem_add_sub_add_of_card_add_le_of_forall_largeSpec {X : Finset G} {κ : ℝ} (hκ : 2 ≤ κ)
    (hX : X.Nonempty) (hXX : #(X + X) ≤ κ * #X) {x : G}
    (hx : ∀ ψ ∈ largeSpec 𝟭_[(X : Set G)] (Real.sqrt (8 * κ)⁻¹), ‖1 - ψ x‖ ≤ 4⁻¹) :
    x ∈ (X + X) - (X + X) := by
  refine mem_add_sub_add_of_forall_largeSpec_norm_one_sub_le (by norm_num) ?_ hx
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left (card_pow_three_le_mul_addEnergy hX hXX)
      (by positivity : (0 : ℝ) ≤ (8 * κ)⁻¹),
    mul_inv_cancel₀ (by positivity : 8 * κ ≠ 0),
    (by exact_mod_cast addEnergy_self_pos hX : (0 : ℝ) < E[X])]

/-- If `#(X + X) ≤ κ * #X` with `2 ≤ κ` and the large spectrum of `𝟭_[X]` at threshold
`√(8 * κ)⁻¹` lies in the span of `Δ`, then every `x` with `‖1 - ψ x‖ ≤ (4 * (#Δ + 1))⁻¹` for
every `ψ ∈ Δ` lies in `X + X - (X + X)`. -/
lemma mem_add_sub_add_of_largeSpec_subset_addSpan {X : Finset G} {κ : ℝ} (hκ : 2 ≤ κ)
    (hX : X.Nonempty) (hXX : #(X + X) ≤ κ * #X) {Δ : Finset (AddChar G ℂ)}
    (hΔ : largeSpec 𝟭_[(X : Set G)] (Real.sqrt (8 * κ)⁻¹) ⊆ Δ.addSpan) {x : G}
    (hx : ∀ ψ ∈ Δ, ‖1 - ψ x‖ ≤ (4 * (#Δ + 1) : ℝ)⁻¹) : x ∈ (X + X) - (X + X) := by
  apply mem_add_sub_add_of_card_add_le_of_forall_largeSpec hκ hX hXX
  intro ψ hψ
  refine ((norm_one_sub_apply_le_sum_of_mem_addSpan (hΔ hψ) x).trans (sum_le_sum hx)).trans ?_
  rw [sum_const, nsmul_eq_mul, mul_inv_le_iff₀ (by positivity)]
  linarith

end LargeSpec

/-- **Chang's lemma** in `ZMod q`. The large spectrum of `𝟭_[X]` at threshold `η` lies in the span
of a subset `Δ` of itself with `#Δ ≤ ⌈changConst * exp 1 * ⌈1 + log (q / #X)⌉₊ / η ^ 2⌉₊`. -/
lemma exists_card_le_largeSpec_subset_addSpan {q : ℕ} [NeZero q] {X : Finset (ZMod q)}
    (hX : X.Nonempty) {η : ℝ} (hη : 0 < η) :
    ∃ Δ ⊆ largeSpec 𝟭_[(X : Set (ZMod q))] η,
      #Δ ≤ ⌈changConst * Real.exp 1 * ⌈1 + Real.log (#X / q : ℝ)⁻¹⌉₊ / η ^ 2⌉₊ ∧
      largeSpec 𝟭_[(X : Set (ZMod q))] η ⊆ Δ.addSpan := by
  simpa [sq, hX.ne_empty] using chang (f := 𝟭_[(X : Set (ZMod q)), ℂ])
    (Function.ne_iff.2 ⟨hX.choose, by simp [hX.choose_spec]⟩) hη

/-! ## Frequencies

Chord widths `‖1 - ψ x‖` are the analytic form of the Bohr condition. The construction of a
progression inside a Bohr set works instead with integer representatives `a` of the products
`r * x` of frequencies with group elements, together with bounds on `|a|`. -/

/-- Every character `ψ` of `ZMod q` is given by a frequency `r`, and
`‖1 - ψ x‖ ≤ 2 * π * |a| / q` for every integer `a` with `(a : ZMod q) = r * x`. -/
lemma exists_frequency_chord_le {q : ℕ} [NeZero q] (ψ : AddChar (ZMod q) ℂ) :
    ∃ r : ZMod q, ∀ (x : ZMod q) (a : ℤ), (a : ZMod q) = r * x →
      ‖1 - ψ x‖ ≤ 2 * Real.pi * |(a : ℝ)| / q := by
  obtain ⟨r, rfl⟩ := AddChar.zmodAddEquiv.surjective ψ
  use r
  intro x a ha
  have hψ : AddChar.zmodAddEquiv r x = ZMod.stdAddChar (a : ZMod q) := by
    rw [ha]
    rfl
  rw [hψ, ZMod.stdAddChar_coe, norm_sub_rev]
  convert Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * a / q) using 1
  · congr 3
    push_cast
    ring
  · simp

end

end ChangFreimanRuzsa
