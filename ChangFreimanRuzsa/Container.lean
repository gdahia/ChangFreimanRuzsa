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

/-! # The coarse cyclic container in Chang's theorem

This is the home of the Ruzsa-model Fourier/Bohr/packing argument. Its output is intentionally an
arbitrary GAP: properness belongs to the following specialized reboxing stage.

The five stages, for `X ⊆ ZMod q` with `q` prime and `|X + X| ≤ κ |X|`:

* **M** (`RuzsaModel.lean`) replaces `X` by a subset `X₁` of density `1 / 8` and a Freiman
  `8`-isomorphic copy `Y ⊆ ZMod m` with `m ≤ κ ^ 16 |X|`, so that the density of `Y` in its ambient
  group is at least `(8 κ ^ 16)⁻¹`, uniformly in `q`;
* **F** (`Fourier.lean`) runs Chang's lemma in `ZMod m`, where the density is bounded below by
  a power of `κ`, so the dissociated generating set `Δ` has size bounded in terms of `κ` alone;
* **B** (`BohrProgression.lean`) puts a proper progression `Q` of dimension `|Δ| + 1` inside
  the chord neighborhood of `Δ`, which Stage F places inside `2Y - 2Y`;
* **T** (`FreimanRigidity.lean`) transports `Q` back to a proper progression
  `Q₁ ⊆ 2X₁ - 2X₁` of `ZMod q` of the same dimension and cardinality;
* **P** (`Packing.lean`) grows `Q₁` by batches of `⌈3 κ⌉` elements of `X₁` until it covers
  `X₁`, and recovers `X` from `X₁` by Ruzsa covering.

All the budgets are explicit functions of `κ`; they are collected in `changContainerExponent`, which
serves as the dimension bound, the logarithm of the container's size relative to `|X|`, and the size
that `X` has to exceed for the model group to be large enough to carry a Bohr progression.

The model group holds no container: only bounded-length additive relations cross the modelling
isomorphism, namely the progression `Q` and, through it, the quadruple relations of Stage T.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open scoped Pointwise

noncomputable section

/-! ## The budgets

Each definition is the explicit bound proved by the corresponding stage. They are deliberately
generous: the pipeline needs a bound of the shape `κ ^ 3 log ^ 2 κ`, and no step below is tight.
-/

/-- Stage F's bound on the size of Chang's dissociated generating set in the model group. It is the
bound of `exists_changLargeSpectrum_generators` at the Chang threshold `η² = (64 κ)⁻¹` and at the
model density `|Y| / m ≥ (8 κ ^ 16)⁻¹`. -/
def changDeltaBound (κ : ℝ) : ℕ :=
  ⌈changConst * Real.exp 1 * (⌈1 + Real.log (8 * κ ^ 16)⌉₊ : ℝ) * (8 * (8 * κ))⌉₊

/-- Stage B's bound on the dimension of the transported progression. -/
def changGapDim (κ : ℝ) : ℕ := changDeltaBound κ + 1

/-- Stage P's batch size. It has to exceed `e κ`, or the growth of the packed set is beaten by the
Plünnecke–Ruzsa bound on the sumsets it lives in. -/
def changBatchSize (κ : ℝ) : ℕ := ⌈3 * κ⌉₊

/-- Stage P's bound on the number of batches. -/
def changPackBound (κ : ℝ) : ℝ := 3 + 4 * κ + 9 * (changGapDim κ : ℝ) ^ 2

/-- Stage P's bound on the number of generators spent on the terminal coverings. -/
def changCoverBound (κ : ℝ) : ℝ := 8 * κ * (changBatchSize κ : ℝ) ^ 2

/-- The single budget of the coarse container stage. It bounds the dimension of the container, the
logarithm of the container's size relative to `|X|`, and the size that `X` has to exceed for the
Ruzsa model of `X` to be large enough to carry a Bohr progression. -/
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
  have h₁ := changCoverBound_nonneg (le_trans zero_le_two hκ)
  have h₂ := changPackBound_nonneg (le_trans zero_le_two hκ)
  have h₃ : (0 : ℝ) ≤ (changGapDim κ : ℝ) := Nat.cast_nonneg _
  have h₄ : (0 : ℝ) ≤ (changBatchSize κ : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- The dimension budget dominates the container's dimension. -/
lemma changContainerExponent_dim_le {κ : ℝ} (hκ : 2 ≤ κ) :
    changCoverBound κ + (changGapDim κ : ℝ) + (changBatchSize κ : ℝ) * changPackBound κ ≤
      changContainerExponent κ := by
  rw [changContainerExponent]
  have h₁ := changCoverBound_nonneg (le_trans zero_le_two hκ)
  have h₂ := changPackBound_nonneg (le_trans zero_le_two hκ)
  have h₃ : (0 : ℝ) ≤ (changGapDim κ : ℝ) := Nat.cast_nonneg _
  have h₄ : (0 : ℝ) ≤ (changBatchSize κ : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- The size budget dominates the container's cardinality exponent. -/
lemma changContainerExponent_size_le {κ : ℝ} (_hκ : 2 ≤ κ) :
    changCoverBound κ + 2 * (changGapDim κ : ℝ) +
      3 * (changBatchSize κ : ℝ) * changPackBound κ + 4 * κ ≤ changContainerExponent κ := by
  rw [changContainerExponent]
  have h₃ : (0 : ℝ) ≤ (changGapDim κ : ℝ) := Nat.cast_nonneg _
  linarith

/-! ## Numerical bounds

Three crude estimates, all of the form "a product of powers is a power of two", which is what keeps
the accounting of the pipeline linear.
-/

/-- `d ≤ 2 ^ d` over the reals. -/
private lemma nat_le_two_pow (d : ℕ) : (d : ℝ) ≤ 2 ^ d := by
  have := Nat.lt_two_pow_self (n := d)
  calc (d : ℝ) ≤ ((2 ^ d : ℕ) : ℝ) := by exact_mod_cast this.le
    _ = 2 ^ d := by push_cast; ring

/-- The dimensional factor of `exists_proper_gap_chordSet`, together with the reciprocal of the
chord width, is at most `2 ^ (12 (|Δ| + 1)²)`. -/
private lemma bohr_factor_le (k : ℕ) :
    (2 : ℝ) ^ ((k + 5) * (k + 1)) * ((k : ℝ) + 1) ^ (k + 1) * (8 * Real.pi * ((k : ℝ) + 1)) ^ k
      ≤ 2 ^ (12 * (k + 1) ^ 2) := by
  have hd : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    linarith
  have hdpow : ((k : ℝ) + 1) ≤ 2 ^ (k + 1) := by
    have := nat_le_two_pow (k + 1)
    push_cast at this
    linarith
  -- the three factors, each bounded by a power of two
  have h₁ : (2 : ℝ) ^ ((k + 5) * (k + 1)) ≤ 2 ^ (5 * (k + 1) ^ 2) :=
    pow_le_pow_right₀ (by norm_num) (by nlinarith [Nat.zero_le k])
  have h₂ : ((k : ℝ) + 1) ^ (k + 1) ≤ 2 ^ ((k + 1) ^ 2) := by
    refine (pow_le_pow_left₀ (by linarith) hdpow (k + 1)).trans (le_of_eq ?_)
    rw [← pow_mul]
    congr 1
    ring
  have h₃ : (8 * Real.pi * ((k : ℝ) + 1)) ^ k ≤ 2 ^ (6 * (k + 1) ^ 2) := by
    have hbase : 8 * Real.pi * ((k : ℝ) + 1) ≤ 2 ^ (5 + (k + 1)) := by
      rw [show (2 : ℝ) ^ (5 + (k + 1)) = 32 * 2 ^ (k + 1) by rw [pow_add]; norm_num]
      have hp : 8 * Real.pi ≤ 32 := by linarith [Real.pi_le_four]
      nlinarith [mul_le_mul_of_nonneg_right hp (by linarith : (0 : ℝ) ≤ (k : ℝ) + 1), hdpow]
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
      exact (P.consBinaryList l).one_lt_length_consGenerator 0 a (by omega) (by omega) ih

lemma one_lt_length_differenceHull (P : GAP G) : ∀ i, 1 < P.differenceHull.length i := by
  intro i
  have := P.length_pos i
  change 1 < 2 * P.length i
  omega

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
      exact Finset.add_subset_add (h S List.mem_cons_self)
        (ih fun T hT ↦ h T (List.mem_cons_of_mem S hT))

/-- The threshold budget dominates what the model group needs to carry a progression. -/
lemma changContainerExponent_threshold_le {κ : ℝ} (hκ : 2 ≤ κ) :
    256 + (changGapDim κ : ℝ) ≤ changContainerExponent κ := by
  rw [changContainerExponent]
  have h₁ := changCoverBound_nonneg (le_trans zero_le_two hκ)
  have h₂ : (0 : ℝ) ≤ 3 * (changBatchSize κ : ℝ) * changPackBound κ :=
    mul_nonneg (by positivity) (changPackBound_nonneg (le_trans zero_le_two hκ))
  have h₃ : (0 : ℝ) ≤ (changGapDim κ : ℝ) := Nat.cast_nonneg _
  linarith

/-! ## The container -/

private lemma two_pow_le_exp_nat (N : ℕ) : (2 : ℝ) ^ N ≤ Real.exp N := by
  rw [show Real.exp (N : ℝ) = Real.exp 1 ^ N by rw [← Real.exp_nat_mul, mul_one]]
  exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le N

private lemma pow_le_exp_mul {κ : ℝ} (hκ : 0 ≤ κ) (n : ℕ) : κ ^ n ≤ Real.exp (n * κ) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ hκ (by linarith [Real.add_one_le_exp κ]) n

/-- **Stages M, F, B and T.** A dense set with small doubling contains a subset `X₁` of density
`1 / 8` together with a proper progression `Q₁ ⊆ 2X - 2X` whose dimension is bounded by
`changGapDim κ` and whose size is at least `|X|` divided by a bound depending only on `κ`.

Everything analytic happens in the model group; only `Q₁` crosses back. -/
private theorem exists_model_gap {q : ℕ} {κ : ℝ} (X : Finset (ZMod q))
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
  -- Stage M: the Ruzsa model
  obtain ⟨m, X₁, φ, hm0, hmle, hX₁X, hX₁card, hφ⟩ :=
    exists_ruzsa_model_of_doubling (s := 8) hq (by norm_num) hXne hXX
  have : NeZero m := ⟨hm0.ne'⟩
  have hX₁cardR : (X.card : ℝ) ≤ 8 * X₁.card := by exact_mod_cast hX₁card
  have hX₁pos : (0 : ℝ) < X₁.card := by linarith
  have hX₁ne : X₁.Nonempty := Finset.card_pos.1 (by exact_mod_cast hX₁pos)
  have hYcard : (X₁.image φ).card = X₁.card := Finset.card_image_of_injOn hφ.bijOn.injOn
  have hYne : (X₁.image φ).Nonempty := Finset.image_nonempty.2 hX₁ne
  have hYpos : (0 : ℝ) < ((X₁.image φ).card : ℝ) := by rw [hYcard]; exact hX₁pos
  have hYm : ((X₁.image φ).card : ℝ) ≤ m := by
    have h := Finset.card_le_univ (X₁.image φ)
    rw [ZMod.card] at h
    exact_mod_cast h
  have hXm : (X.card : ℝ) ≤ 8 * m := by
    rw [hYcard] at hYm
    linarith
  -- the density of the model is bounded below by a power of `κ`
  have hdensity : ((((X₁.image φ).card : ℝ) / m)⁻¹) ≤ 8 * κ ^ 16 := by
    rw [inv_div, div_le_iff₀ hYpos, hYcard]
    have hmle' : (m : ℝ) ≤ κ ^ 16 * X.card := by
      simpa only [show 2 * 8 = 16 from rfl] using hmle
    nlinarith [pow_pos hκ0 16]
  -- the doubling constant transports to the model group
  have hYY : ((X₁.image φ + X₁.image φ).card : ℝ) ≤ (8 * κ) * (X₁.image φ).card := by
    have h3 : ((X₁.image φ + X₁.image φ).card : ℝ) ≤ ((X + X).card : ℝ) := by
      refine Nat.cast_le.2 (le_trans ?_ (Finset.card_le_card (Finset.add_subset_add hX₁X hX₁X)))
      exact card_add_le_of_isAddFreimanIso (IsAddFreimanIso.mono (hmn := by norm_num) hφ.invFunOn)
    rw [hYcard]
    nlinarith
  -- Stage F: Chang's lemma in the model group
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
  -- Stage F: the chord neighborhood of `Δ` lies in `2Y - 2Y`
  have hchord := changGenerators_chord_subset_fourfold (X₁.image φ) (κ := 8 * κ) (by linarith)
    hYne hYY hΔspan
  have hk1 : ((Δ.card : ℝ) + 1) ≤ (changGapDim κ : ℝ) := by
    rw [changGapDim]
    push_cast
    linarith [(Nat.cast_le (α := ℝ)).2 hΔbound]
  -- the model group is large enough to carry a Bohr progression
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
  -- Stage B: a proper progression inside the chord neighborhood
  obtain ⟨Q, hQproper, hQdim, hQcert, hQsize⟩ :=
    exists_proper_gap_chordSet Δ (ε := ((4 : ℝ) * (Δ.card + 1))⁻¹) hεm
      (by
        rw [inv_le_one_iff₀]
        right
        linarith [Nat.cast_nonneg (α := ℝ) Δ.card])
  have hQsub : Q.carrier ⊆ (X₁.image φ + X₁.image φ) - (X₁.image φ + X₁.image φ) := fun z hz ↦
    hchord (hQcert (Finset.mem_coe.2 hz))
  -- Stage T: transport back to `ZMod q`
  obtain ⟨Q₁, hQ₁proper, hQ₁dim, hQ₁card, hQ₁sub⟩ := exists_transported_gap hφ Q hQproper hQsub
  have hQ₁pos : (0 : ℝ) < Q₁.carrier.card := by
    exact_mod_cast Finset.card_pos.2 Q₁.nonempty
  have hQ₁dimle : (Q₁.dim : ℝ) ≤ (changGapDim κ : ℝ) := by
    rw [hQ₁dim, hQdim, changGapDim]
    exact Nat.cast_le.2 (Nat.succ_le_succ hΔbound)
  have hQ₁subX : Q₁.carrier ⊆ (X + X) - (X + X) :=
    hQ₁sub.trans (Finset.sub_subset_sub (Finset.add_subset_add hX₁X hX₁X)
      (Finset.add_subset_add hX₁X hX₁X))
  -- the Bohr count, in the crude form the accounting uses
  have hQlow : (X.card : ℝ) ≤ 8 * 2 ^ (12 * changGapDim κ ^ 2) * Q₁.carrier.card := by
    have hc : (0 : ℝ) < 8 * Real.pi * ((Δ.card : ℝ) + 1) := by positivity
    rw [show ((4 : ℝ) * (Δ.card + 1))⁻¹ / (2 * Real.pi) = (8 * Real.pi * ((Δ.card : ℝ) + 1))⁻¹ by
      rw [div_eq_mul_inv, ← mul_inv]; congr 1; ring, inv_pow, ← div_eq_mul_inv,
      div_le_iff₀ (pow_pos hc Δ.card)] at hQsize
    have hQsize' : (m : ℝ) ≤ ((2 : ℝ) ^ ((Δ.card + 5) * (Δ.card + 1)) *
        ((Δ.card : ℝ) + 1) ^ (Δ.card + 1) *
        (8 * Real.pi * ((Δ.card : ℝ) + 1)) ^ Δ.card) * Q₁.carrier.card := by
      rw [hQ₁card]
      refine hQsize.trans (le_of_eq ?_)
      ring
    have hmono : (2 : ℝ) ^ (12 * (Δ.card + 1) ^ 2) ≤ 2 ^ (12 * changGapDim κ ^ 2) :=
      pow_le_pow_right₀ (by norm_num)
        (Nat.mul_le_mul_left 12 (Nat.pow_le_pow_left (Nat.succ_le_succ hΔbound) 2))
    have hstep : (m : ℝ) ≤ 2 ^ (12 * changGapDim κ ^ 2) * Q₁.carrier.card :=
      hQsize'.trans (mul_le_mul_of_nonneg_right ((bohr_factor_le Δ.card).trans hmono) hQ₁pos.le)
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (12 * changGapDim κ ^ 2)]
  exact ⟨X₁, Q₁, hX₁X, hX₁card, hQ₁proper, hQ₁dimle, hQ₁subX, hQlow⟩

/-- The coarse-container interface consumed by the geometric part of Chang's theorem.

The dimension bound is the coarse stage's own budget `changContainerExponent κ`. Reducing it to the
Freiman dimension of `X` — the bound the downstream result actually needs — is the job of
`chang_coordinate_reduction`, not of this stage.

No upper bound on `|X|` is assumed: the Fourier and Bohr stages run inside the model group `ZMod m`,
whose size is controlled by `|X|` alone, so the coarse stage never needs room inside `ZMod q`. -/
theorem exists_coarseGAP_container {q : ℕ} {κ : ℝ} (X : Finset (ZMod q))
    (hq : Nat.Prime q) (hκ : 2 ≤ κ)
    (hXX : ((X + X).card : ℝ) ≤ κ * X.card)
    (hXlower : Real.exp (changContainerExponent κ) < X.card) :
    ∃ P : GAP (ZMod q),
      X ⊆ P.carrier ∧
        (∀ i, 1 < P.length i) ∧
        ((P.dim : ℝ) ≤ changContainerExponent κ) ∧
        (P.carrier.card : ℝ) ≤ Real.exp (changContainerExponent κ) * X.card := by
  have : NeZero q := ⟨hq.pos.ne'⟩
  have hκ0 : (0 : ℝ) < κ := by linarith
  have hXpos : (0 : ℝ) < X.card := (Real.exp_pos _).trans hXlower
  have hXne : X.Nonempty := Finset.card_pos.1 (by exact_mod_cast hXpos)
  obtain ⟨X₁, Q₁, hX₁X, hX₁card, hQ₁proper, hQ₁dimle, hQ₁subX, hQlow⟩ :=
    exists_model_gap X hq hκ hXX hXlower
  have hX₁cardR : (X.card : ℝ) ≤ 8 * X₁.card := by exact_mod_cast hX₁card
  have hX₁pos : (0 : ℝ) < X₁.card := by linarith
  have hX₁ne : X₁.Nonempty := Finset.card_pos.1 (by exact_mod_cast hX₁pos)
  have hQ₁pos : (0 : ℝ) < Q₁.carrier.card := by
    exact_mod_cast Finset.card_pos.2 Q₁.nonempty
  -- Stage P: batch packing inside `ZMod q`
  have hm₀κ : 3 * κ ≤ (changBatchSize κ : ℝ) := by
    rw [changBatchSize]
    exact Nat.le_ceil _
  have hm₀ : 2 ≤ changBatchSize κ := by
    have : (2 : ℝ) ≤ (changBatchSize κ : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨batches, F, hbatches, hpacked, -, hFcard, hcover⟩ :=
    exists_chang_batch_packing X₁ Q₁.carrier Q₁.nonempty (changBatchSize κ) hm₀
  have hSsub : Q₁.carrier + batchSum batches ⊆ (batches.length + 2) • X - 2 • X := by
    intro z hz
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.1 hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.1 (hQ₁subX hu)
    refine Finset.mem_sub.2 ⟨a + v, ?_, b, ?_, by abel⟩
    · rw [show batches.length + 2 = 2 + batches.length from by ring, add_nsmul]
      refine Finset.add_mem_add ?_
        (batchSum_subset_nsmul batches X (fun S hS ↦ (hbatches S hS).1.trans hX₁X) hv)
      rwa [two_nsmul]
    · rwa [two_nsmul]
  have hPR : (((batches.length + 2) • X - 2 • X).card : ℝ) ≤
      κ ^ (batches.length + 4) * X.card := by
    have hcast := (NNRat.cast_le (K := ℝ)).2
      (Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hXne X (batches.length + 2) 2)
    push_cast [NNRat.cast_pow] at hcast
    apply hcast.trans
    rw [show batches.length + 2 + 2 = batches.length + 4 from by ring]
    gcongr
    exact (div_le_iff₀ hXpos).2 hXX
  have hgrow : (3 : ℝ) ^ batches.length * Q₁.carrier.card ≤ κ ^ 4 * X.card := by
    refine le_of_mul_le_mul_right ?_ (pow_pos hκ0 batches.length)
    rw [show (3 : ℝ) ^ batches.length * Q₁.carrier.card * κ ^ batches.length =
        (Q₁.carrier.card : ℝ) * (3 * κ) ^ batches.length from by rw [mul_pow]; ring,
      show κ ^ 4 * (X.card : ℝ) * κ ^ batches.length = κ ^ (batches.length + 4) * X.card from by
        rw [pow_add]; ring]
    apply le_trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hm₀κ batches.length) hQ₁pos.le)
    refine le_trans ?_ hPR
    rw [← Nat.cast_pow, ← Nat.cast_mul, ← hpacked]
    exact Nat.cast_le.2 (Finset.card_le_card hSsub)
  have hQ₁le : (Q₁.carrier.card : ℝ) ≤ κ ^ 4 * X.card := by
    refine le_trans ?_ hgrow
    nlinarith [one_le_pow₀ (show (1 : ℝ) ≤ 3 by norm_num) (n := batches.length)]
  have hlen : (batches.length : ℝ) ≤ changPackBound κ := by
    have h3len : (3 : ℝ) ^ batches.length ≤ 8 * κ ^ 4 * 2 ^ (12 * changGapDim κ ^ 2) := by
      refine le_of_mul_le_mul_right (hgrow.trans ?_) hQ₁pos
      refine le_trans (mul_le_mul_of_nonneg_left hQlow (pow_pos hκ0 4).le) (le_of_eq ?_)
      ring
    have hlog := Real.log_le_log (by positivity) h3len
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow] at hlog
    have hl3 : (1 : ℝ) ≤ Real.log 3 := by
      have h := Real.log_le_log (Real.exp_pos 1)
        (show Real.exp 1 ≤ 3 by linarith [Real.exp_one_lt_d9])
      rwa [Real.log_exp] at h
    have hl8 : Real.log 8 ≤ 3 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      push_cast
      linarith [Real.log_two_lt_d9]
    push_cast at hlog
    rw [changPackBound]
    linarith [mul_le_mul_of_nonneg_left hl3 (Nat.cast_nonneg (α := ℝ) batches.length),
      mul_le_mul_of_nonneg_left (show Real.log 2 ≤ 0.7 by linarith [Real.log_two_lt_d9])
        (show (0 : ℝ) ≤ 12 * (changGapDim κ : ℝ) ^ 2 by positivity),
      Real.log_le_self hκ0.le, sq_nonneg (changGapDim κ : ℝ)]
  -- Ruzsa covering recovers `X` from `X₁`
  obtain ⟨F', -, hF'card, hXcov⟩ := Finset.ruzsa_covering_add (K := 8 * κ) hX₁ne
    (by
      have h1 : ((X + X₁).card : ℝ) ≤ ((X + X).card : ℝ) :=
        Nat.cast_le.2 (Finset.card_le_card (Finset.add_subset_add_left hX₁X))
      nlinarith)
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
  -- the container
  let W := F' + (F - F)
  set S := Q₁.carrier + batchSum batches with hSdef
  set R := Q₁.consBinaryList (batchElements batches) with hRdef
  set U := R.differenceHull.differenceHull with hUdef
  have hbatchlen : (batchElements batches).length = changBatchSize κ * batches.length :=
    batchElements_length fun Sb hSb ↦ (hbatches Sb hSb).2
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
    have hml : (changBatchSize κ : ℝ) * (batches.length : ℝ) ≤
        (changBatchSize κ : ℝ) * changPackBound κ :=
      mul_le_mul_of_nonneg_left hlen (Nat.cast_nonneg _)
    linarith
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
    have hml : (changBatchSize κ : ℝ) * (batches.length : ℝ) ≤
        (changBatchSize κ : ℝ) * changPackBound κ :=
      mul_le_mul_of_nonneg_left hlen (Nat.cast_nonneg _)
    linarith

end

end ChangFreimanRuzsa
