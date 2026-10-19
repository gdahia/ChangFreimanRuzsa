/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.CoordinateReduction
public import ChangFreimanRuzsa.Integers
import ChangFreimanRuzsa.Bound

/-!
# Chang's theorem with dimension at most the Freiman dimension

Let $q$ be a prime and let $X \subseteq \mathbb{Z}/q\mathbb{Z}$ satisfy $|X + X| \le \kappa |X|$.
Write $c_\kappa$ for `containerExponent κ` and $F_\kappa$ for `freimanDimExponent κ`. If
$e^{c_\kappa} < |X|$ and $e^{F_\kappa} |X| \le q$, then $X$ lies in a $2$-proper generalized
arithmetic progression of dimension at most `freimanDim X` and of size at most $e^{F_\kappa} |X|$.
A finite nonempty set $X \subseteq \mathbb{Z}$ with $|X + X| \le \kappa |X|$ lies in a $2$-proper
progression of dimension at most `freimanDim X` and of size at most $e^{E_\kappa} |X|$, where
$E_\kappa$ is `intFreimanDimExponent κ`.

In `ZMod q` the proof has three stages. `exists_gap_zmod_subset_dim_le_card_le` puts $X$ in a
progression of dimension at most $c_\kappa$ and of size at most $e^{c_\kappa} |X|$,
`exists_twoProperGAP_carrier_subset_dim_le_card_le_of_injOn_nsmul` replaces that progression by a
$2$-proper one, and `exists_twoProperGAP_dim_le_freimanDim_of_injOn_nsmul` replaces the $2$-proper
progression by one of dimension at most `freimanDim X`. For sets of integers,
`exists_twoProperGAP_dim_le_freimanDim_of_isAddTorsionFree` is applied to the $2$-proper
progression of `exists_twoProperGAP_of_small_sumset`.

## Main definitions

* `freimanDimExponent κ`: the exponent in the size bound of the progression in `ZMod q`.
* `intFreimanDimExponent κ`: the exponent in the size bound of the progression for sets of
  integers.

## Main statements

* `exists_twoProperGAP_zmod_dim_le_freimanDim`: Chang's theorem in `ZMod q` with dimension at most
  `freimanDim X`.
* `exists_twoProperGAP_int_dim_le_freimanDim`: Chang's theorem for sets of integers with dimension
  at most `freimanDim X`.
* `freimanDimExponent_le`: `freimanDimExponent κ` is at most $10^{53} \kappa^{20}$ for
  $\kappa \ge 2$.
* `intFreimanDimExponent_le`: `intFreimanDimExponent κ` is at most $10^{59} \kappa^{20}$ for
  $\kappa \ge 2$.
-/

public section

open Finset SumOfSetsInSeveralDimensions
open scoped Pointwise

namespace ChangFreimanRuzsa

/-- The exponent in the size bound of Chang's theorem in `ZMod q` with the dimension bounded by the
Freiman dimension. -/
@[expose] noncomputable def freimanDimExponent (κ : ℝ) : ℝ :=
  (properizationConstant + coordinateReductionConstant) * (containerExponent κ + 2) ^ 4 +
    containerExponent κ

/-- The exponent in the size bound of Chang's theorem for sets of integers with the dimension
bounded by the Freiman dimension. -/
@[expose] noncomputable def intFreimanDimExponent (κ : ℝ) : ℝ :=
  intExponent κ + coordinateReductionConstant * (containerExponent (2 * κ) + 2) ^ 4

/-- The second and third stages of Chang's theorem, in an abelian group in which the multiples
$n a$ with $n < N$ of every nonzero $a$ are distinct. Write $c_\kappa$ for
`containerExponent κ` and $F_\kappa$ for `freimanDimExponent κ`. Let a nonempty set $X$
lie in a progression $P$ of dimension at most $c_\kappa$ and of size at most $e^{c_\kappa} |X|$. If
$e^{F_\kappa} |X| \le N$, then $X$ lies in a $2$-proper progression of dimension at most
`freimanDim X` and of size at most $e^{F_\kappa} |X|$. -/
lemma exists_twoProperGAP_dim_le_freimanDim_of_subset_gap {G : Type*} [DecidableEq G]
    [AddCommGroup G] {N : ℕ} {κ : ℝ} {X : Finset G} {P : GAP G}
    (hG : ∀ a : G, a ≠ 0 → Set.InjOn (fun n : ℕ ↦ n • a) (Set.Iio N)) (hX : X.Nonempty)
    (hXP : X ⊆ P.carrier) (hPdim : (P.dim : ℝ) ≤ containerExponent κ)
    (hPcard : (#P.carrier : ℝ) ≤ Real.exp (containerExponent κ) * #X)
    (hXN : Real.exp (freimanDimExponent κ) * #X ≤ N) :
    ∃ Q : GAP G, Q.TwoProper ∧ X ⊆ Q.carrier ∧ (∀ i, 1 < Q.length i) ∧
      Q.dim ≤ freimanDim X ∧ (#Q.carrier : ℝ) ≤ Real.exp (freimanDimExponent κ) * #X := by
  have hPX : Real.exp (properizationConstant * ((P.dim : ℝ) + 2) ^ 4) * #P.carrier ≤
      Real.exp (freimanDimExponent κ) * #X := by
    rw [freimanDimExponent, Real.exp_add, mul_assoc]
    gcongr
    · exact add_nonneg properizationConstant_pos.le coordinateReductionConstant_pos.le
    · exact le_add_of_nonneg_right coordinateReductionConstant_pos.le
  obtain ⟨P₂, hP₂, hPP₂, -, hP₂dim, hP₂card⟩ :=
    exists_twoProperGAP_carrier_subset_dim_le_card_le_of_injOn_nsmul P hG (hPX.trans hXN)
  have hP₂X : Real.exp (coordinateReductionConstant * ((P₂.dim : ℝ) + 2) ^ 4) * #P₂.carrier ≤
      Real.exp (freimanDimExponent κ) * #X := by
    rw [freimanDimExponent, add_comm properizationConstant, add_mul, Real.exp_add,
      Real.exp_add, mul_assoc, mul_assoc]
    gcongr
    · exact coordinateReductionConstant_pos.le
    · exact (Nat.cast_le.2 hP₂dim).trans hPdim
    · refine hP₂card.trans ?_
      gcongr
      exact properizationConstant_pos.le
  obtain ⟨Q, hQ, hXQ, hlen, hQdim, hQcard⟩ :=
    exists_twoProperGAP_dim_le_freimanDim_of_injOn_nsmul hG hX hP₂ (hXP.trans hPP₂)
      (hP₂X.trans hXN)
  exact ⟨Q, hQ, hXQ, hlen, hQdim, hQcard.trans hP₂X⟩

/-- **Chang's theorem** in `ZMod q` for a prime $q$, with the dimension bounded by the Freiman
dimension. Write $c_\kappa$ for `containerExponent κ` and $F_\kappa$ for
`freimanDimExponent κ`. A set $X$ with $|X + X| \le \kappa |X|$, $e^{c_\kappa} < |X|$ and
$e^{F_\kappa} |X| \le q$ is contained in a $2$-proper generalized arithmetic progression of
dimension at most `freimanDim X` and of size at most $e^{F_\kappa} |X|$. -/
theorem exists_twoProperGAP_zmod_dim_le_freimanDim {q : ℕ} {κ : ℝ} (X : Finset (ZMod q))
    (hq : q.Prime) (hκ : 2 ≤ κ) (hXX : (#(X + X) : ℝ) ≤ κ * #X)
    (hXlower : Real.exp (containerExponent κ) < #X)
    (hXupper : Real.exp (freimanDimExponent κ) * #X ≤ q) :
    ∃ Q : GAP (ZMod q), Q.TwoProper ∧ X ⊆ Q.carrier ∧ (∀ i, 1 < Q.length i) ∧
      Q.dim ≤ freimanDim X ∧ (#Q.carrier : ℝ) ≤ Real.exp (freimanDimExponent κ) * #X := by
  obtain ⟨P, hXP, -, hPdim, hPcard⟩ := exists_gap_zmod_subset_dim_le_card_le X hq hκ hXX hXlower
  exact exists_twoProperGAP_dim_le_freimanDim_of_subset_gap
    (fun _ ↦ GAP.injOn_nsmul_of_prime hq) (card_pos.1 (mod_cast (Real.exp_pos _).trans hXlower))
    hXP hPdim hPcard hXupper

/-- **Chang's theorem** for sets of integers, with the dimension bounded by the Freiman dimension.
Write $E_\kappa$ for `intFreimanDimExponent κ`. A finite nonempty set $X \subseteq \mathbb{Z}$
with $|X + X| \le \kappa |X|$ is contained in a $2$-proper generalized arithmetic progression of
dimension at most `freimanDim X` and of size at most $e^{E_\kappa} |X|$. -/
theorem exists_twoProperGAP_int_dim_le_freimanDim {κ : ℝ} (X : Finset ℤ) (hX : X.Nonempty)
    (hκ : 2 ≤ κ) (hXX : (#(X + X) : ℝ) ≤ κ * #X) :
    ∃ Q : GAP ℤ, Q.TwoProper ∧ X ⊆ Q.carrier ∧ (∀ i, 1 < Q.length i) ∧
      Q.dim ≤ freimanDim X ∧ (#Q.carrier : ℝ) ≤ Real.exp (intFreimanDimExponent κ) * #X := by
  obtain ⟨P, hP, hXP, hPdim, hPcard⟩ := exists_twoProperGAP_of_small_sumset X hX hκ hXX
  obtain ⟨Q, hQ, hXQ, hlen, hQdim, hQcard⟩ :=
    exists_twoProperGAP_dim_le_freimanDim_of_isAddTorsionFree hX hP hXP
  refine ⟨Q, hQ, hXQ, hlen, hQdim, hQcard.trans ?_⟩
  rw [intFreimanDimExponent, add_comm (intExponent κ), Real.exp_add, mul_assoc]
  gcongr
  exact coordinateReductionConstant_pos.le

/-- `freimanDimExponent κ` is at most $10^{53} \kappa^{20}$ for $\kappa \ge 2$. -/
lemma freimanDimExponent_le {κ : ℝ} (hκ : 2 ≤ κ) :
    freimanDimExponent κ ≤ 10 ^ 53 * κ ^ 20 := by
  unfold freimanDimExponent coordinateReductionConstant properizationConstant
  linarith [containerExponent_le hκ, containerExponent_add_two_pow_le hκ,
    pow_le_pow_right₀ (one_le_two.trans hκ) (by norm_num : 5 ≤ 20),
    pow_pos (zero_lt_two.trans_le hκ) 20]

/-- `intFreimanDimExponent κ` is at most $10^{59} \kappa^{20}$ for $\kappa \ge 2$. -/
lemma intFreimanDimExponent_le {κ : ℝ} (hκ : 2 ≤ κ) :
    intFreimanDimExponent κ ≤ 10 ^ 59 * κ ^ 20 := by
  have h := containerExponent_le (by linarith : 2 ≤ 2 * κ)
  have h' := containerExponent_add_two_pow_le (by linarith : 2 ≤ 2 * κ)
  unfold intFreimanDimExponent intExponent zmodExponent coordinateReductionConstant
    properizationConstant
  rw [mul_pow] at h h'
  norm_num at h h' ⊢
  linarith [pow_le_pow_right₀ (by linarith : 1 ≤ κ) (by norm_num : 5 ≤ 20),
    one_le_pow₀ (n := 20) (by linarith : 1 ≤ κ)]

end ChangFreimanRuzsa
