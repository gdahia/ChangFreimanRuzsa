/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.Packing
public import APAPCompat.Prereqs.Chang
import ChangFreimanRuzsa.BohrProgression
import ChangFreimanRuzsa.Fourier
import ChangFreimanRuzsa.FreimanRigidity
import ChangFreimanRuzsa.RuzsaModel
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Combinatorics.Additive.RuzsaCovering
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! # A coarse progression containing a set of small doubling

Let $q$ be prime and let $X \subseteq \mathbb{Z}/q\mathbb{Z}$ satisfy $|X + X| \le \kappa |X|$. If
$|X|$ is large in terms of $\kappa$, then $X$ is contained in a (not necessarily proper) GAP whose
dimension, and whose size relative to $|X|$, are bounded in terms of $\kappa$ alone. The proof has
five steps.

1. (`RuzsaModel.lean`) There are a subset $X_1 \subseteq X$ with $|X| \le 8 |X_1|$ and a Freiman
   $8$-isomorphic copy $Y \subseteq \mathbb{Z}/m\mathbb{Z}$ of $X_1$ with $m \le \kappa^{16} |X|$,
   so that $Y$ has density at least $(8 \kappa^{16})^{-1}$ in $\mathbb{Z}/m\mathbb{Z}$.
2. (`Fourier.lean`) Chang's lemma in $\mathbb{Z}/m\mathbb{Z}$ gives a dissociated set $\Delta$ of
   characters whose size is bounded in terms of $\kappa$ and whose chord neighbourhood lies in
   $2Y - 2Y$.
3. (`BohrProgression.lean`) The chord neighbourhood of $\Delta$ contains a proper progression $Q$ of
   dimension $|\Delta| + 1$.
4. (`FreimanRigidity.lean`) The Freiman isomorphism carries $Q$ to a proper progression
   $Q_1 \subseteq 2X_1 - 2X_1$ of $\mathbb{Z}/q\mathbb{Z}$ with the same dimension and cardinality.
5. (`Packing.lean`) Adding to $Q_1$ batches of $\lceil 3 \kappa \rceil$ elements of $X_1$ until it
   covers $X_1$, and covering $X$ by few translates of $X_1$, gives the progression containing $X$.
   This step, `exists_coarseGAP_container_of_model_gap`, holds in every abelian group, and
   `Integers.lean` applies it to sets of integers.

All bounds are explicit functions of $\kappa$. They are collected in `changContainerExponent`, which
bounds the dimension of the container, the logarithm of its size relative to $|X|$, and the size
that $|X|$ has to exceed for $\mathbb{Z}/m\mathbb{Z}$ to contain a Bohr progression.

## Main statements

* `exists_model_gap`: steps 1 to 4.
* `exists_coarseGAP_container_of_model_gap`: step 5, in an arbitrary abelian group.
* `exists_coarseGAP_container`: the coarse container in $\mathbb{Z}/q\mathbb{Z}$.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open scoped Pointwise

noncomputable section

/-! ## The bounds

Each definition is an explicit function of $\kappa$ bounding one quantity of the argument. None of
them is optimal.
-/

/-- The bound on the size of the dissociated set $\Delta$ given by Chang's lemma in
$\mathbb{Z}/m\mathbb{Z}$. It is the bound of `exists_changLargeSpectrum_generators` at the threshold
$\eta^2 = (64 \kappa)^{-1}$ and the density $|Y| / m \ge (8 \kappa^{16})^{-1}$. -/
def changDeltaBound (κ : ℝ) : ℕ :=
  ⌈changConst * Real.exp 1 * (⌈1 + Real.log (8 * κ ^ 16)⌉₊ : ℝ) * (8 * (8 * κ))⌉₊

/-- The bound on the dimension $|\Delta| + 1$ of the Bohr progression $Q$ and of its image $Q_1$
in $\mathbb{Z}/q\mathbb{Z}$. -/
def changGapDim (κ : ℝ) : ℕ := changDeltaBound κ + 1

/-- The batch size $\lceil 3 \kappa \rceil$ of the packing argument. Since it exceeds $e \kappa$,
the growth of the packed set outpaces the Plünnecke–Ruzsa bound on the sumsets containing it. -/
def changBatchSize (κ : ℝ) : ℕ := ⌈3 * κ⌉₊

/-- The bound on the number of batches in the packing argument. -/
def changPackBound (κ : ℝ) : ℝ := 3 + 4 * κ + 9 * (changGapDim κ : ℝ) ^ 2

/-- The bound on the number of translates added at the end of the packing argument to cover $X$. -/
def changCoverBound (κ : ℝ) : ℝ := 8 * κ * (changBatchSize κ : ℝ) ^ 2

/-- The exponent $E(\kappa)$ of the coarse container. It bounds the dimension of the container, the
logarithm of its size relative to $|X|$, and the logarithm of the size that $|X|$ has to exceed for
the Ruzsa model of $X$ to contain a Bohr progression. -/
def changContainerExponent (κ : ℝ) : ℝ :=
  256 + 3 * (changGapDim κ : ℝ) + 4 * κ + changCoverBound κ +
    3 * (changBatchSize κ : ℝ) * changPackBound κ

lemma changPackBound_nonneg {κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ changPackBound κ := by
  rw [changPackBound]
  positivity

lemma changCoverBound_nonneg {κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ changCoverBound κ := by
  rw [changCoverBound]
  positivity

lemma changContainerExponent_pos {κ : ℝ} (hκ : 2 ≤ κ) : 0 < changContainerExponent κ := by
  rw [changContainerExponent]
  nlinarith [changCoverBound_nonneg (by linarith : 0 ≤ κ),
    changPackBound_nonneg (by linarith : 0 ≤ κ), Nat.cast_nonneg (α := ℝ) (changGapDim κ),
    Nat.cast_nonneg (α := ℝ) (changBatchSize κ)]

/-- The exponent bounds the dimension of the container. -/
lemma changContainerExponent_dim_le {κ : ℝ} (hκ : 2 ≤ κ) :
    changCoverBound κ + (changGapDim κ : ℝ) + (changBatchSize κ : ℝ) * changPackBound κ ≤
      changContainerExponent κ := by
  rw [changContainerExponent]
  nlinarith [changCoverBound_nonneg (by linarith : 0 ≤ κ),
    changPackBound_nonneg (by linarith : 0 ≤ κ), Nat.cast_nonneg (α := ℝ) (changGapDim κ),
    Nat.cast_nonneg (α := ℝ) (changBatchSize κ)]

/-- The exponent bounds the logarithm of the size of the container relative to $|X|$. -/
lemma changContainerExponent_size_le {κ : ℝ} (_hκ : 2 ≤ κ) :
    changCoverBound κ + 2 * (changGapDim κ : ℝ) +
      3 * (changBatchSize κ : ℝ) * changPackBound κ + 4 * κ ≤ changContainerExponent κ := by
  rw [changContainerExponent]
  linarith [Nat.cast_nonneg (α := ℝ) (changGapDim κ)]

/-! ## Numerical bounds

Two estimates bounding products of powers by a power of two.
-/

/-- $d \le 2^d$ for every natural number $d$, in the reals. -/
private lemma nat_le_two_pow (d : ℕ) : (d : ℝ) ≤ 2 ^ d := by
  exact_mod_cast (Nat.lt_two_pow_self (n := d)).le

/-- The dimensional factor of `exists_proper_gap_chordSet`, together with the reciprocal of the
chord width, is at most $2^{12 (k + 1)^2}$, where $k = |\Delta|$. -/
private lemma bohr_factor_le (k : ℕ) :
    (2 : ℝ) ^ ((k + 5) * (k + 1)) * ((k : ℝ) + 1) ^ (k + 1) * (8 * Real.pi * ((k : ℝ) + 1)) ^ k
      ≤ 2 ^ (12 * (k + 1) ^ 2) := by
  have hdpow : ((k : ℝ) + 1) ≤ 2 ^ (k + 1) := by
    simpa using nat_le_two_pow (k + 1)
  have h₁ : (2 : ℝ) ^ ((k + 5) * (k + 1)) ≤ 2 ^ (5 * (k + 1) ^ 2) :=
    pow_le_pow_right₀ (by norm_num) (by nlinarith [Nat.zero_le k])
  have h₂ : ((k : ℝ) + 1) ^ (k + 1) ≤ 2 ^ ((k + 1) ^ 2) := by
    refine (pow_le_pow_left₀ (by positivity) hdpow (k + 1)).trans ?_
    rw [← pow_mul, sq]
  have h₃ : (8 * Real.pi * ((k : ℝ) + 1)) ^ k ≤ 2 ^ (6 * (k + 1) ^ 2) := by
    have hbase : 8 * Real.pi * ((k : ℝ) + 1) ≤ 2 ^ (5 + (k + 1)) := by
      rw [pow_add]
      nlinarith [mul_le_mul_of_nonneg_right Real.pi_le_four (by positivity : (0 : ℝ) ≤ k + 1)]
    refine ((pow_le_pow_left₀ (by positivity) hbase k).trans ?_)
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by nlinarith [Nat.zero_le k])
  refine le_trans (mul_le_mul (mul_le_mul h₁ h₂ (by positivity) (by positivity)) h₃
    (by positivity) (by positivity)) (le_of_eq ?_)
  rw [← pow_add, ← pow_add]
  congr 1
  ring

/-! ## Auxiliary facts about the packing GAPs -/

namespace GAP

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

lemma one_lt_length_consGenerator (P : GAP G) (originShift step : G) {length : ℕ}
    (hlength : 0 < length) (h1 : 1 < length) (h : ∀ i, 1 < P.length i) :
    ∀ i, 1 < (P.consGenerator originShift step length hlength).length i := by
  intro i
  induction i using Fin.cases with
  | zero => exact h1
  | succ j => exact h j

lemma one_lt_length_consBinaryList (P : GAP G) (l : List G) (h : ∀ i, 1 < P.length i) :
    ∀ i, 1 < (P.consBinaryList l).length i := by
  induction l with
  | nil => exact h
  | cons a l ih =>
      exact (P.consBinaryList l).one_lt_length_consGenerator 0 a (by grind) (by grind) ih

lemma one_lt_length_differenceHull (P : GAP G) : ∀ i, 1 < P.differenceHull.length i := by
  intro i
  change 1 < 2 * P.length i
  grind [P.length_pos i]

end GAP

/-- Each batch is a subset of `A`, so a choice of one element per batch is a sum of
`batches.length` elements of `A`. -/
private lemma batchSum_subset_nsmul {G : Type*} [DecidableEq G] [AddCommGroup G]
    (batches : List (Finset G)) (A : Finset G) (h : ∀ S ∈ batches, S ⊆ A) :
    batchSum batches ⊆ batches.length • A := by
  induction batches with
  | nil => simp [batchSum]
  | cons S l ih =>
      rw [batchSum, List.length_cons, succ_nsmul']
      exact Finset.add_subset_add (h S List.mem_cons_self) (ih (by grind))

/-- The exponent bounds the logarithm of the size that $|X|$ has to exceed for the Ruzsa model of
$X$ to contain a Bohr progression. -/
lemma changContainerExponent_threshold_le {κ : ℝ} (hκ : 2 ≤ κ) :
    256 + (changGapDim κ : ℝ) ≤ changContainerExponent κ := by
  rw [changContainerExponent]
  nlinarith [changCoverBound_nonneg (by linarith : 0 ≤ κ),
    changPackBound_nonneg (by linarith : 0 ≤ κ), Nat.cast_nonneg (α := ℝ) (changGapDim κ),
    Nat.cast_nonneg (α := ℝ) (changBatchSize κ)]

/-! ## The container -/

private lemma two_pow_le_exp_nat (N : ℕ) : (2 : ℝ) ^ N ≤ Real.exp N := by
  rw [← Real.exp_one_pow]
  exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le N

private lemma pow_le_exp_mul {κ : ℝ} (hκ : 0 ≤ κ) (n : ℕ) : κ ^ n ≤ Real.exp (n * κ) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ hκ (by linarith [Real.add_one_le_exp κ]) n

/-- Let $q$ be prime and let $X \subseteq \mathbb{Z}/q\mathbb{Z}$ satisfy $|X + X| \le \kappa |X|$
and $|X| > e^{E(\kappa)}$, where $E$ is `changContainerExponent`. Then $X$ has a subset $X_1$ with
$|X| \le 8 |X_1|$, and $2X - 2X$ contains a proper progression $Q_1$ of dimension at most
$d$ = `changGapDim κ` with $|X| \le 8 \cdot 2^{12 d^2} |Q_1|$. -/
lemma exists_model_gap {q : ℕ} {κ : ℝ} (X : Finset (ZMod q))
    (hq : Nat.Prime q) (hκ : 2 ≤ κ)
    (hXX : ((X + X).card : ℝ) ≤ κ * X.card)
    (hXlower : Real.exp (changContainerExponent κ) < X.card) :
    ∃ (X₁ : Finset (ZMod q)) (Q₁ : GAP (ZMod q)),
      X₁ ⊆ X ∧ X.card ≤ 8 * X₁.card ∧ Q₁.Proper ∧
        (Q₁.dim : ℝ) ≤ (changGapDim κ : ℝ) ∧
        Q₁.carrier ⊆ (X + X) - (X + X) ∧
        (X.card : ℝ) ≤ 8 * 2 ^ (12 * changGapDim κ ^ 2) * Q₁.carrier.card := by
  have : NeZero q := ⟨hq.pos.ne'⟩
  have hκ0 : (0 : ℝ) < κ := by linarith
  have hXpos : (0 : ℝ) < X.card := (Real.exp_pos _).trans hXlower
  have hXne : X.Nonempty := Finset.card_pos.1 (by exact_mod_cast hXpos)
  obtain ⟨m, X₁, φ, hm0, hmle, hX₁X, hX₁card, hφ⟩ :=
    exists_ruzsa_model_of_doubling (s := 8) hq (by norm_num) hXne hXX
  have : NeZero m := ⟨hm0.ne'⟩
  have hX₁cardR : (X.card : ℝ) ≤ 8 * X₁.card := by exact_mod_cast hX₁card
  have hYcard : ((X₁.image φ).card : ℝ) = X₁.card := by
    rw [Finset.card_image_of_injOn hφ.bijOn.injOn]
  have hYne : (X₁.image φ).Nonempty := (Finset.card_pos.1 (by grind [hXne.card_pos])).image φ
  have hYm : ((X₁.image φ).card : ℝ) ≤ m := by
    exact_mod_cast (Finset.card_le_univ (X₁.image φ)).trans_eq (ZMod.card m)
  have hXm : (X.card : ℝ) ≤ 8 * m := by
    linarith
  have hdensity : ((((X₁.image φ).card : ℝ) / m)⁻¹) ≤ 8 * κ ^ 16 := by
    rw [inv_div, div_le_iff₀ (by linarith), hYcard]
    have hmle' : (m : ℝ) ≤ κ ^ 16 * X.card := by simpa using hmle
    linarith [mul_le_mul_of_nonneg_left hX₁cardR (pow_pos hκ0 16).le]
  have hYY : ((X₁.image φ + X₁.image φ).card : ℝ) ≤ (8 * κ) * (X₁.image φ).card := by
    have h3 : ((X₁.image φ + X₁.image φ).card : ℝ) ≤ ((X + X).card : ℝ) := by
      refine Nat.cast_le.2 (le_trans ?_ (Finset.card_le_card (Finset.add_subset_add hX₁X hX₁X)))
      exact card_add_le_of_isAddFreimanIso (IsAddFreimanIso.mono (hmn := by norm_num) hφ.invFunOn)
    rw [hYcard]
    nlinarith
  obtain ⟨Δ, -, hΔcard, hΔspan⟩ :=
    exists_changLargeSpectrum_generators (X₁.image φ) hYne
      (η := Real.sqrt ((8 * (8 * κ))⁻¹)) (Real.sqrt_pos.2 (by positivity))
  have hΔbound : Δ.card ≤ changDeltaBound κ := by
    rw [changDeltaBound]
    refine hΔcard.trans (Nat.ceil_le_ceil ?_)
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (8 * (8 * κ))⁻¹), div_inv_eq_mul]
    have hceil : (⌈1 + Real.log ((((X₁.image φ).card : ℝ) / m)⁻¹)⌉₊ : ℝ) ≤
        (⌈1 + Real.log (8 * κ ^ 16)⌉₊ : ℝ) := by
      refine Nat.cast_le.2 (Nat.ceil_le_ceil ?_)
      have := Real.log_le_log (by positivity) hdensity
      linarith
    have hpos : (0 : ℝ) ≤ changConst * Real.exp 1 := by positivity
    have h64 : (0 : ℝ) ≤ 8 * (8 * κ) := by positivity
    gcongr
  have hchord := changGenerators_chord_subset_fourfold (X₁.image φ) (κ := 8 * κ) (by linarith)
    hYne hYY hΔspan
  have hk1 : ((Δ.card : ℝ) + 1) ≤ (changGapDim κ : ℝ) := by
    rw [changGapDim]
    exact_mod_cast Nat.succ_le_succ hΔbound
  have hXbig : 256 * (changGapDim κ : ℝ) ≤ X.card := by
    refine le_trans ?_ hXlower.le
    refine le_trans ?_ (Real.exp_le_exp.2 (changContainerExponent_threshold_le hκ))
    rw [Real.exp_add]
    nlinarith [Real.add_one_le_exp (256 : ℝ), Real.add_one_le_exp (changGapDim κ : ℝ),
      Real.exp_pos (changGapDim κ : ℝ), Real.exp_pos (256 : ℝ),
      Nat.cast_nonneg (α := ℝ) (changGapDim κ)]
  have hεm : 2 * Real.pi ≤ ((4 : ℝ) * (Δ.card + 1))⁻¹ * m := by
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
    have hπ : 2 * Real.pi * (4 * ((Δ.card : ℝ) + 1)) ≤ 32 * ((Δ.card : ℝ) + 1) := by
      nlinarith [Real.pi_le_four, Nat.cast_nonneg (α := ℝ) Δ.card]
    nlinarith [hXm, hXbig, hk1]
  obtain ⟨Q, hQproper, hQdim, hQcert, hQsize⟩ :=
    exists_proper_gap_chordSet Δ (ε := ((4 : ℝ) * (Δ.card + 1))⁻¹) hεm
      (inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) Δ.card]))
  have hQsub : Q.carrier ⊆ (X₁.image φ + X₁.image φ) - (X₁.image φ + X₁.image φ) := fun z hz ↦
    hchord (hQcert (Finset.mem_coe.2 hz))
  obtain ⟨Q₁, hQ₁proper, hQ₁dim, hQ₁card, hQ₁sub⟩ := exists_transported_gap hφ Q hQproper hQsub
  have hQ₁pos : (0 : ℝ) < Q₁.carrier.card := by
    exact_mod_cast Finset.card_pos.2 Q₁.nonempty
  have hQ₁dimle : (Q₁.dim : ℝ) ≤ (changGapDim κ : ℝ) := by
    rw [hQ₁dim, hQdim, changGapDim]
    exact Nat.cast_le.2 (Nat.succ_le_succ hΔbound)
  have hQ₁subX : Q₁.carrier ⊆ (X + X) - (X + X) :=
    hQ₁sub.trans (Finset.sub_subset_sub (Finset.add_subset_add hX₁X hX₁X)
      (Finset.add_subset_add hX₁X hX₁X))
  have hQlow : (X.card : ℝ) ≤ 8 * 2 ^ (12 * changGapDim κ ^ 2) * Q₁.carrier.card := by
    have hε : ((4 : ℝ) * (Δ.card + 1))⁻¹ / (2 * Real.pi) =
        (8 * Real.pi * ((Δ.card : ℝ) + 1))⁻¹ := by
      rw [div_eq_mul_inv, ← mul_inv]
      ring
    rw [hε, inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity), ← hQ₁card] at hQsize
    have hmono : (2 : ℝ) ^ (12 * (Δ.card + 1) ^ 2) ≤ 2 ^ (12 * changGapDim κ ^ 2) :=
      pow_le_pow_right₀ (by norm_num)
        (Nat.mul_le_mul_left 12 (Nat.pow_le_pow_left (Nat.succ_le_succ hΔbound) 2))
    linarith [mul_le_mul_of_nonneg_right ((bohr_factor_le Δ.card).trans hmono) hQ₁pos.le]
  exact ⟨X₁, Q₁, hX₁X, hX₁card, hQ₁proper, hQ₁dimle, hQ₁subX, hQlow⟩

/-- Let $X$ be a nonempty finite subset of an abelian group with $|X + X| \le \kappa |X|$. Given a
subset $X_1 \subseteq X$ with $|X| \le 8 |X_1|$ and a proper progression $Q_1 \subseteq 2X - 2X$
with the bounds of `exists_model_gap`, the set $X$ lies in a progression with all lengths at least
$2$, of dimension at most $E$ and of size at most $e^{E} |X|$, where $E$ is
`changContainerExponent κ`. The group may be infinite. -/
lemma exists_coarseGAP_container_of_model_gap {G : Type*} [DecidableEq G] [AddCommGroup G]
    {κ : ℝ} {X X₁ : Finset G} {Q₁ : GAP G} (hXne : X.Nonempty) (hκ : 2 ≤ κ)
    (hXX : ((X + X).card : ℝ) ≤ κ * X.card) (hX₁X : X₁ ⊆ X) (hX₁card : X.card ≤ 8 * X₁.card)
    (hQ₁proper : Q₁.Proper) (hQ₁dimle : (Q₁.dim : ℝ) ≤ (changGapDim κ : ℝ))
    (hQ₁subX : Q₁.carrier ⊆ (X + X) - (X + X))
    (hQlow : (X.card : ℝ) ≤ 8 * 2 ^ (12 * changGapDim κ ^ 2) * Q₁.carrier.card) :
    ∃ P : GAP G,
      X ⊆ P.carrier ∧
        (∀ i, 1 < P.length i) ∧
        ((P.dim : ℝ) ≤ changContainerExponent κ) ∧
        (P.carrier.card : ℝ) ≤ Real.exp (changContainerExponent κ) * X.card := by
  have hκ0 : (0 : ℝ) < κ := by linarith
  have hXpos : (0 : ℝ) < X.card := Nat.cast_pos.2 hXne.card_pos
  have hX₁cardR : (X.card : ℝ) ≤ 8 * X₁.card := by exact_mod_cast hX₁card
  have hX₁ne : X₁.Nonempty := Finset.card_pos.1 (by grind [hXne.card_pos])
  have hQ₁pos : (0 : ℝ) < Q₁.carrier.card := by
    exact_mod_cast Finset.card_pos.2 Q₁.nonempty
  have hm₀κ : 3 * κ ≤ (changBatchSize κ : ℝ) := by
    rw [changBatchSize]
    exact Nat.le_ceil _
  have hm₀ : 2 ≤ changBatchSize κ := by
    exact_mod_cast (by linarith : (2 : ℝ) ≤ changBatchSize κ)
  have hgrow : ∀ batches : List (Finset G),
      (∀ S ∈ batches, S ⊆ X₁ ∧ S.card = changBatchSize κ) →
      (Q₁.carrier + batchSum batches).card =
        Q₁.carrier.card * changBatchSize κ ^ batches.length →
      (3 : ℝ) ^ batches.length * Q₁.carrier.card ≤ κ ^ 4 * X.card := by
    intro batches hbatches hpacked
    obtain ⟨hbsub, -⟩ := forall₂_and.1 hbatches
    have hSsub : Q₁.carrier + batchSum batches ⊆ (batches.length + 2) • X - 2 • X := by
      intro z hz
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.1 hz
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.1 (hQ₁subX hu)
      refine Finset.mem_sub.2 ⟨a + v, ?_, b, ?_, by abel⟩
      · rw [add_comm batches.length 2, add_nsmul]
        refine Finset.add_mem_add ?_
          (batchSum_subset_nsmul batches X (fun S hS ↦ (hbsub S hS).trans hX₁X) hv)
        rwa [two_nsmul]
      · rwa [two_nsmul]
    have hPR : (((batches.length + 2) • X - 2 • X).card : ℝ) ≤
        κ ^ (batches.length + 4) * X.card := by
      have hcast := (NNRat.cast_le (K := ℝ)).2
        (Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hXne X (batches.length + 2) 2)
      push_cast [NNRat.cast_pow] at hcast
      apply hcast.trans
      gcongr
      exact (div_le_iff₀ hXpos).2 hXX
    refine le_of_mul_le_mul_right ?_ (pow_pos hκ0 batches.length)
    have h3 : (3 : ℝ) ^ batches.length * Q₁.carrier.card * κ ^ batches.length =
        Q₁.carrier.card * (3 * κ) ^ batches.length := by
      ring
    have h4 : κ ^ 4 * (X.card : ℝ) * κ ^ batches.length = κ ^ (batches.length + 4) * X.card := by
      ring
    rw [h3, h4]
    apply le_trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hm₀κ batches.length) hQ₁pos.le)
    refine le_trans ?_ hPR
    rw [← Nat.cast_pow, ← Nat.cast_mul, ← hpacked]
    exact Nat.cast_le.2 (Finset.card_le_card hSsub)
  have hB : ∀ batches : List (Finset G),
      (∀ S ∈ batches, S ⊆ X₁ ∧ S.card = changBatchSize κ) →
      (Q₁.carrier + batchSum batches).card =
        Q₁.carrier.card * changBatchSize κ ^ batches.length →
      batches.length ≤ ⌈κ ^ 4 * X.card⌉₊ := by
    intro batches hbatches hpacked
    have h₁ : (batches.length : ℝ) ≤ 3 ^ batches.length :=
      mod_cast (Nat.lt_pow_self (by norm_num : 1 < 3)).le
    have h₂ : (1 : ℝ) ≤ Q₁.carrier.card := mod_cast Q₁.nonempty.card_pos
    exact Nat.cast_le.1 ((h₁.trans (le_mul_of_one_le_right (by positivity) h₂)).trans
      ((hgrow batches hbatches hpacked).trans (Nat.le_ceil _)))
  obtain ⟨batches, F, hbatches, hpacked, -, hFcard, hcover⟩ :=
    exists_chang_batch_packing X₁ Q₁.carrier Q₁.nonempty (changBatchSize κ) (by grind) _ hB
  have hgrow := hgrow batches hbatches hpacked
  have hQ₁le : (Q₁.carrier.card : ℝ) ≤ κ ^ 4 * X.card := by
    refine le_trans ?_ hgrow
    nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3) (n := batches.length)]
  have hlen : (batches.length : ℝ) ≤ changPackBound κ := by
    have h3len : (3 : ℝ) ^ batches.length ≤ 8 * κ ^ 4 * 2 ^ (12 * changGapDim κ ^ 2) := by
      refine le_of_mul_le_mul_right (hgrow.trans ?_) hQ₁pos
      refine le_trans (mul_le_mul_of_nonneg_left hQlow (pow_pos hκ0 4).le) (le_of_eq ?_)
      ring
    have hlog := Real.log_le_log (by positivity) h3len
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow] at hlog
    have hl3 : (1 : ℝ) ≤ Real.log 3 := by
      simpa using Real.log_le_log (Real.exp_pos 1)
        (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ 3)
    have hl8 : Real.log 8 ≤ 3 := by
      have h := Real.log_pow (2 : ℝ) 3
      norm_num at h
      linarith [Real.log_two_lt_d9]
    push_cast at hlog
    rw [changPackBound]
    linarith [mul_le_mul_of_nonneg_left hl3 (Nat.cast_nonneg (α := ℝ) batches.length),
      mul_le_mul_of_nonneg_left (by linarith [Real.log_two_lt_d9] : Real.log 2 ≤ 0.7)
        (by positivity : (0 : ℝ) ≤ 12 * (changGapDim κ : ℝ) ^ 2),
      Real.log_le_self hκ0.le, sq_nonneg (changGapDim κ : ℝ)]
  obtain ⟨F', -, hF'card, hXcov⟩ := Finset.ruzsa_covering_add (K := 8 * κ) hX₁ne
    (by
      nlinarith [(Nat.cast_le (α := ℝ)).2
        (Finset.card_le_card (Finset.add_subset_add_left (s := X) hX₁X))])
  have hFm : (F.card : ℝ) ≤ (changBatchSize κ : ℝ) := Nat.cast_le.2 hFcard.le
  have hWnat : (F' + (F - F)).card ≤ F'.card * (F.card * F.card) :=
    Finset.card_add_le.trans (Nat.mul_le_mul le_rfl Finset.card_sub_le)
  have hWcast : ((F' + (F - F)).card : ℝ) ≤ (F'.card : ℝ) * (F.card : ℝ) * (F.card : ℝ) := by
    refine le_trans (Nat.cast_le.2 hWnat) (le_of_eq ?_)
    push_cast
    ring
  have hWcard : ((F' + (F - F)).card : ℝ) ≤ changCoverBound κ := by
    apply hWcast.trans
    rw [changCoverBound, sq, ← mul_assoc]
    exact mul_le_mul (mul_le_mul hF'card hFm (Nat.cast_nonneg _) (by positivity)) hFm
      (Nat.cast_nonneg _) (by positivity)
  let W := F' + (F - F)
  set S := Q₁.carrier + batchSum batches with hSdef
  set R := Q₁.consBinaryList (batchElements batches) with hRdef
  set U := R.differenceHull.differenceHull with hUdef
  obtain ⟨-, hbcard⟩ := forall₂_and.1 hbatches
  have hbatchlen : (batchElements batches).length = changBatchSize κ * batches.length :=
    batchElements_length hbcard
  have hRdim : R.dim = Q₁.dim + changBatchSize κ * batches.length := by
    rw [hRdef, GAP.dim_consBinaryList, hbatchlen]
  have hSR : S ⊆ R.carrier := by
    rw [hSdef, hRdef]
    exact (Finset.add_subset_add_left
      (batchSum_subset_binaryListSum_batchElements batches)).trans
      (GAP.add_binaryListSum_subset_consBinaryList Q₁ (batchElements batches))
  have hSST : S - S ⊆ R.differenceHull.carrier :=
    (Finset.sub_subset_sub hSR hSR).trans R.sub_carrier_subset_differenceHull
  have hUsub : S - S - (S - S) ⊆ U.carrier := by
    rw [hUdef]
    exact (Finset.sub_subset_sub hSST hSST).trans
      R.differenceHull.sub_carrier_subset_differenceHull
  have hXW : X ⊆ U.carrier + W := by
    intro x hx
    obtain ⟨f', hf', y, hy, rfl⟩ := Finset.mem_add.1 (hXcov hx)
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.1 hy
    obtain ⟨g₁, hg₁, z₁, hz₁, rfl⟩ := Finset.mem_add.1 (hcover ha)
    obtain ⟨g₂, hg₂, z₂, hz₂, rfl⟩ := Finset.mem_add.1 (hcover hb)
    refine Finset.mem_add.2 ⟨z₁ - z₂, hUsub (Finset.mem_sub.2 ⟨z₁, hz₁, z₂, hz₂, rfl⟩),
      f' + (g₁ - g₂), ?_, by abel⟩
    exact Finset.add_mem_add hf' (Finset.mem_sub.2 ⟨g₁, hg₁, g₂, hg₂, rfl⟩)
  refine ⟨U.consBinaryList (finsetList W), ?_, ?_, ?_, ?_⟩
  · refine hXW.trans ((Finset.add_subset_add_left fun w hw ↦
      mem_binaryListSum_of_mem (mem_finsetList.2 hw)).trans ?_)
    exact GAP.add_binaryListSum_subset_consBinaryList U (finsetList W)
  · refine U.one_lt_length_consBinaryList (finsetList W) ?_
    rw [hUdef]
    exact GAP.one_lt_length_differenceHull R.differenceHull
  · rw [GAP.dim_consBinaryList, finsetList_length, hUdef, GAP.differenceHull_dim,
      GAP.differenceHull_dim, hRdim]
    push_cast
    refine le_trans ?_ (changContainerExponent_dim_le hκ)
    linarith [mul_le_mul_of_nonneg_left hlen (Nat.cast_nonneg (α := ℝ) (changBatchSize κ))]
  · have hnat : (U.consBinaryList (finsetList W)).carrier.card ≤
        2 ^ (W.card + 2 * R.dim + changBatchSize κ * batches.length) * Q₁.carrier.card := by
      apply (GAP.card_consBinaryList_le U (finsetList W)).trans
      rw [finsetList_length, hUdef, GAP.boxVolume_differenceHull,
        GAP.boxVolume_differenceHull, GAP.differenceHull_dim, hRdef,
        GAP.boxVolume_consBinaryList, hbatchlen, GAP.boxVolume,
        ← Q₁.card_eq_prod_length hQ₁proper, ← hRdef]
      apply le_of_eq
      rw [pow_add, pow_add, two_mul, pow_add]
      ring
    have hcardle : ((U.consBinaryList (finsetList W)).carrier.card : ℝ) ≤
        (2 : ℝ) ^ (W.card + 2 * R.dim + changBatchSize κ * batches.length) *
          Q₁.carrier.card := by
      refine le_trans (Nat.cast_le.2 hnat) (le_of_eq ?_)
      push_cast
      ring
    refine hcardle.trans (le_trans (mul_le_mul_of_nonneg_left hQ₁le (by positivity)) ?_)
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hXpos.le
    apply le_trans (mul_le_mul (two_pow_le_exp_nat _) (pow_le_exp_mul hκ0.le 4)
      (by positivity) (Real.exp_nonneg _))
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 (le_trans ?_ (changContainerExponent_size_le hκ))
    rw [hRdim]
    push_cast
    linarith [mul_le_mul_of_nonneg_left hlen (Nat.cast_nonneg (α := ℝ) (changBatchSize κ))]

/-- Let $q$ be prime and let $X \subseteq \mathbb{Z}/q\mathbb{Z}$ satisfy $|X + X| \le \kappa |X|$
and $|X| > e^{E}$, where $E$ is `changContainerExponent κ`. Then $X$ lies in a GAP with all lengths
at least $2$, of dimension at most $E$ and of size at most $e^{E} |X|$.

No upper bound on $|X|$ in terms of $q$ is needed, because the Fourier-analytic steps take place in
$\mathbb{Z}/m\mathbb{Z}$ with $m \le \kappa^{16} |X|$. The lemma
`exists_twoProperGAP_dim_le_freimanDim` then bounds the dimension by the Freiman dimension of
$X$. -/
lemma exists_coarseGAP_container {q : ℕ} {κ : ℝ} (X : Finset (ZMod q))
    (hq : Nat.Prime q) (hκ : 2 ≤ κ)
    (hXX : ((X + X).card : ℝ) ≤ κ * X.card)
    (hXlower : Real.exp (changContainerExponent κ) < X.card) :
    ∃ P : GAP (ZMod q),
      X ⊆ P.carrier ∧
        (∀ i, 1 < P.length i) ∧
        ((P.dim : ℝ) ≤ changContainerExponent κ) ∧
        (P.carrier.card : ℝ) ≤ Real.exp (changContainerExponent κ) * X.card := by
  obtain ⟨X₁, Q₁, hX₁X, hX₁card, hQ₁proper, hQ₁dimle, hQ₁subX, hQlow⟩ :=
    exists_model_gap X hq hκ hXX hXlower
  exact exists_coarseGAP_container_of_model_gap
    (Finset.card_pos.1 (by exact_mod_cast (Real.exp_pos _).trans hXlower)) hκ hXX hX₁X hX₁card
    hQ₁proper hQ₁dimle hQ₁subX hQlow

end

end ChangFreimanRuzsa
