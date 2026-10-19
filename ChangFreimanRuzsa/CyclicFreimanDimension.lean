/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.Container
public import ChangFreimanRuzsa.CoordinateReduction
import ChangFreimanRuzsa.Bound
import SumOfSetsInSeveralDimensions.FreimanDimensionSumsetBounds

/-!
# Chang's theorem with dimension at most the Freiman dimension

Let $q$ be a prime and let $X \subseteq \mathbb{Z}/q\mathbb{Z}$ satisfy $|X + X| \le \kappa |X|$.
Write $c_\kappa$ for `containerExponent κ` and $F_\kappa$ for `freimanDimExponent κ`. If
$e^{c_\kappa} < |X|$ and $e^{F_\kappa} |X| \le q$, then $X$ lies in a $2$-proper generalized
arithmetic progression of dimension at most `freimanDim X` and of size at most $e^{F_\kappa} |X|$.
The same holds for a finite set $X \subseteq \mathbb{Z}$ with $e^{c_\kappa} < |X|$.

The proof has three stages. `exists_gap_zmod_subset_dim_le_card_le` puts $X$ in a progression of
dimension at most $c_\kappa$ and of size at most $e^{c_\kappa} |X|$,
`exists_twoProperGAP_carrier_subset_dim_le_card_le_of_injOn_nsmul` replaces that progression by a
$2$-proper one, and `exists_twoProperGAP_dim_le_freimanDim_of_injOn_nsmul` replaces the $2$-proper
progression by one of dimension at most `freimanDim X`. For sets of integers the first stage is
`exists_gap_int_subset_dim_le_card_le`.

The Freiman dimension of $X$ is at most $2\kappa - 1$ when $|X + X| \le \kappa |X|$, so the
progression also has dimension at most $2\kappa - 1$.

## Main definitions

* `freimanDimExponent κ`: the exponent in the size bound of the progression.

## Main statements

* `exists_twoProperGAP_zmod_dim_le_freimanDim`: Chang's theorem in `ZMod q` with dimension at most
  `freimanDim X`.
* `exists_twoProperGAP_int_dim_le_freimanDim`: Chang's theorem for sets of integers with dimension
  at most `freimanDim X`.
* `exists_twoProperGAP_zmod_dim_le_two_mul_sub_one` and
  `exists_twoProperGAP_int_dim_le_two_mul_sub_one`: the same with dimension at most $2\kappa - 1$.
* `freimanDimExponent_le`: `freimanDimExponent κ` is at most $10^{53} \kappa^{20}$ for
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
Write $c_\kappa$ for `containerExponent κ` and $F_\kappa$ for `freimanDimExponent κ`. A
finite set $X \subseteq \mathbb{Z}$ with $|X + X| \le \kappa |X|$ and $e^{c_\kappa} < |X|$ is
contained in a $2$-proper generalized arithmetic progression of dimension at most `freimanDim X`
and of size at most $e^{F_\kappa} |X|$. -/
theorem exists_twoProperGAP_int_dim_le_freimanDim {κ : ℝ} (X : Finset ℤ) (hκ : 2 ≤ κ)
    (hXX : (#(X + X) : ℝ) ≤ κ * #X) (hXlower : Real.exp (containerExponent κ) < #X) :
    ∃ Q : GAP ℤ, Q.TwoProper ∧ X ⊆ Q.carrier ∧ (∀ i, 1 < Q.length i) ∧
      Q.dim ≤ freimanDim X ∧ (#Q.carrier : ℝ) ≤ Real.exp (freimanDimExponent κ) * #X := by
  obtain ⟨P, hXP, -, hPdim, hPcard⟩ := exists_gap_int_subset_dim_le_card_le X hκ hXX hXlower
  exact exists_twoProperGAP_dim_le_freimanDim_of_subset_gap
    (fun _ ↦ GAP.injOn_nsmul_of_isAddTorsionFree _)
    (card_pos.1 (mod_cast (Real.exp_pos _).trans hXlower)) hXP hPdim hPcard (Nat.le_ceil _)

/-- **Chang's theorem** in `ZMod q` for a prime $q$, with dimension at most $2\kappa - 1$. Under the
hypotheses of `exists_twoProperGAP_zmod_dim_le_freimanDim`, the Freiman dimension of $X$ is at most
$2\kappa - 1$. -/
theorem exists_twoProperGAP_zmod_dim_le_two_mul_sub_one {q : ℕ} {κ : ℝ}
    (X : Finset (ZMod q)) (hq : q.Prime) (hκ : 2 ≤ κ) (hXX : (#(X + X) : ℝ) ≤ κ * #X)
    (hXlower : Real.exp (containerExponent κ) < #X)
    (hXupper : Real.exp (freimanDimExponent κ) * #X ≤ q) :
    ∃ Q : GAP (ZMod q), Q.TwoProper ∧ X ⊆ Q.carrier ∧ (∀ i, 1 < Q.length i) ∧
      (Q.dim : ℝ) ≤ 2 * κ - 1 ∧ (#Q.carrier : ℝ) ≤ Real.exp (freimanDimExponent κ) * #X := by
  obtain ⟨Q, hQ, hXQ, hlen, hQdim, hQcard⟩ :=
    exists_twoProperGAP_zmod_dim_le_freimanDim X hq hκ hXX hXlower hXupper
  exact ⟨Q, hQ, hXQ, hlen, (Nat.cast_le.2 hQdim).trans (freimanDim_le_two_mul_sub_one_of_card_add_le
    (card_pos.1 (mod_cast (Real.exp_pos _).trans hXlower)) hXX), hQcard⟩

/-- **Chang's theorem** for sets of integers, with dimension at most $2\kappa - 1$. Under the
hypotheses of `exists_twoProperGAP_int_dim_le_freimanDim`, the Freiman dimension of $X$ is at most
$2\kappa - 1$. -/
theorem exists_twoProperGAP_int_dim_le_two_mul_sub_one {κ : ℝ} (X : Finset ℤ) (hκ : 2 ≤ κ)
    (hXX : (#(X + X) : ℝ) ≤ κ * #X) (hXlower : Real.exp (containerExponent κ) < #X) :
    ∃ Q : GAP ℤ, Q.TwoProper ∧ X ⊆ Q.carrier ∧ (∀ i, 1 < Q.length i) ∧
      (Q.dim : ℝ) ≤ 2 * κ - 1 ∧ (#Q.carrier : ℝ) ≤ Real.exp (freimanDimExponent κ) * #X := by
  obtain ⟨Q, hQ, hXQ, hlen, hQdim, hQcard⟩ :=
    exists_twoProperGAP_int_dim_le_freimanDim X hκ hXX hXlower
  exact ⟨Q, hQ, hXQ, hlen, (Nat.cast_le.2 hQdim).trans (freimanDim_le_two_mul_sub_one_of_card_add_le
    (card_pos.1 (mod_cast (Real.exp_pos _).trans hXlower)) hXX), hQcard⟩

/-- `freimanDimExponent κ` is at most $10^{53} \kappa^{20}$ for $\kappa \ge 2$. -/
lemma freimanDimExponent_le {κ : ℝ} (hκ : 2 ≤ κ) :
    freimanDimExponent κ ≤ 10 ^ 53 * κ ^ 20 := by
  unfold freimanDimExponent coordinateReductionConstant properizationConstant
  linarith [containerExponent_le hκ, containerExponent_add_two_pow_le hκ,
    pow_le_pow_right₀ (one_le_two.trans hκ) (by norm_num : 5 ≤ 20),
    pow_pos (zero_lt_two.trans_le hκ) 20]

end ChangFreimanRuzsa
