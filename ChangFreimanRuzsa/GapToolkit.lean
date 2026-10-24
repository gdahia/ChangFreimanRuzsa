/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Combinatorics.Additive.FreimanHom
public import Mathlib.Data.Pi.Interval
public import Mathlib.Data.Int.Interval
public import ChangFreimanRuzsa.GeneralizedArithmeticProgression
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.BigOperators.Fin

/-!
# Numbered steps, sizes and coefficients of generalized arithmetic progressions

This file develops the basic theory of (not necessarily proper) generalized arithmetic progressions
(GAPs) and their interaction with Freiman isomorphisms.

A GAP `P` has the steps `v` with `P.bound v ≠ 0`. Numbering them as `P.step i` for `i : Fin P.dim`,
with lengths `P.length i = P.bound (P.step i) + 1 ≥ 2`, gives the usual description of the points
of `P` as `P.origin + ∑ i, w i • P.step i` with `w i < P.length i`.

## Main definitions

* `GAP.ofSteps`: the GAP with prescribed origin, numbered steps and lengths.
* `GAP.step` and `GAP.length`: the numbered steps and lengths of a GAP.
* `GAP.size`: the number `∏ v ∈ P.bound.support, (P.bound v + 1)` of coefficient vectors.
* `GAP.coeff` and `GAP.coordinateMap`: coefficients of an element of a GAP.
* `GAP.map` and `GAP.shift`: images of a GAP under additive homomorphisms and translations.
* `stepsHom`, `stepHom` and `symBox`: the homomorphism from `ℤ ^ d` to `G` given by the steps,
  and the symmetric box of differences of coefficient vectors.

## Main statements

* `GAP.carrier_add`: the points of `P + Q` are the sums of a point of `P` and a point of `Q`.
* `GAP.proper_iff_card_eq_size`: a GAP `P` is proper if and only if it has `P.size` elements.
* `GAP.proper_iff_injective` and `GAP.twoProper_iff_injective`: properness and `2`-properness in
  terms of the numbered steps and lengths.
* `GAP.coordinateMap_bijOn_iff`: a GAP is proper if and only if its coordinate map is a bijection
  onto its box.
* `GAP.coordinateMap_isAddFreimanIso_iff`: the coordinate map of a GAP is a Freiman
  `2`-isomorphism onto its box in `ℤ ^ d` if and only if the GAP is `2`-proper.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open scoped Pointwise

noncomputable section

/-! ## Decompositions of finitely supported functions -/

section Decomposition

variable {ι : Type*}

/-- A function `c ≤ a + b` with values in `ℕ` is the sum of functions `c₁ ≤ a` and `c₂ ≤ b`. -/
lemma exists_add_eq_of_le_add {a b c : ι →₀ ℕ} (h : c ≤ a + b) :
    ∃ c₁ ≤ a, ∃ c₂ ≤ b, c₁ + c₂ = c := by
  refine ⟨c ⊓ a, inf_le_right, c - c ⊓ a, ?_, add_tsub_cancel_of_le inf_le_left⟩
  rw [Finsupp.le_def] at h ⊢
  intro v
  grind [Finsupp.inf_apply, Finsupp.tsub_apply, Finsupp.add_apply, h v]

/-- A function below `Finsupp.single v m` is `Finsupp.single v n` for some `n`. -/
lemma eq_single_of_le_single {c : ι →₀ ℕ} {v : ι} {m : ℕ} (h : c ≤ Finsupp.single v m) :
    c = Finsupp.single v (c v) := by
  classical
  ext u
  grind [Finsupp.le_def.1 h u]

/-- The functions below `∑ i, Finsupp.single (s i) (n i)` are the functions
`∑ i, Finsupp.single (s i) (w i)` with `w ≤ n`. -/
lemma le_sum_single_iff {d : ℕ} {s : Fin d → ι} {n : Fin d → ℕ} {c : ι →₀ ℕ} :
    c ≤ ∑ i, Finsupp.single (s i) (n i) ↔
      ∃ w : Fin d → ℕ, (∀ i, w i ≤ n i) ∧ ∑ i, Finsupp.single (s i) (w i) = c := by
  constructor
  · intro h
    induction d generalizing c with
    | zero =>
      refine ⟨0, fun i ↦ i.elim0, ?_⟩
      simp_all
    | succ d ih =>
      rw [Fin.sum_univ_succ] at h
      obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := exists_add_eq_of_le_add h
      obtain ⟨w, hw, rfl⟩ := ih hc₂
      refine ⟨Fin.cons (c₁ (s 0)) w, ?_, ?_⟩
      · intro i
        cases i using Fin.cases
        · simpa using Finsupp.le_def.1 hc₁ (s 0)
        · simpa using hw _
      · conv_rhs => rw [eq_single_of_le_single hc₁]
        simp [Fin.sum_univ_succ]
  · rintro ⟨w, hw, rfl⟩
    apply Finset.sum_le_sum
    intro i _
    exact Finsupp.single_mono (hw i)

end Decomposition

/-- The points `gapMap origin step length w` are the points `origin + ∑ i, c i • step i` with
natural numbers `c i < length i`. -/
lemma mem_image_gapMap_iff {G : Type*} [DecidableEq G] [AddCommMonoid G] {d : ℕ} {origin : G}
    {step : Fin d → G} {length : Fin d → ℕ} {x : G} :
    x ∈ Finset.univ.image (gapMap origin step length) ↔
      ∃ c : Fin d → ℕ, (∀ i, c i < length i) ∧ origin + ∑ i, c i • step i = x := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨w, -, rfl⟩
    exact ⟨fun i ↦ w i, fun i ↦ (w i).isLt, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨fun i ↦ ⟨c i, hc i⟩, Finset.mem_univ _, rfl⟩

instance {G : Type*} [DecidableEq G] [AddCommMonoid G] : CoeOut (GAP G) (Finset G) where
  coe P := P.carrier

namespace GAP

variable {G : Type*} [AddCommMonoid G]

/-! ## Points and sums -/

lemma ext {P Q : GAP G} (horigin : P.origin = Q.origin) (hbound : P.bound = Q.bound) : P = Q := by
  cases P
  cases Q
  congr

@[simp] lemma origin_add (P Q : GAP G) : (P + Q).origin = P.origin + Q.origin := rfl

@[simp] lemma bound_add (P Q : GAP G) : (P + Q).bound = P.bound + Q.bound := rfl

lemma eval_eq_linearCombination (P : GAP G) (c : G →₀ ℕ) :
    P.eval c = P.origin + Finsupp.linearCombination ℕ id c := by
  rw [eval, Finsupp.linearCombination_apply]
  rfl

@[simp] lemma eval_zero (P : GAP G) : P.eval 0 = P.origin := by
  simp [eval]

lemma eval_add (P Q : GAP G) (c₁ c₂ : G →₀ ℕ) :
    (P + Q).eval (c₁ + c₂) = P.eval c₁ + Q.eval c₂ := by
  simp only [eval_eq_linearCombination, map_add, origin_add]
  exact add_add_add_comm _ _ _ _

lemma eval_sum_single (P : GAP G) {d : ℕ} (s : Fin d → G) (w : Fin d → ℕ) :
    P.eval (∑ i, Finsupp.single (s i) (w i)) = P.origin + ∑ i, w i • s i := by
  simp [eval_eq_linearCombination, map_sum]

section Carrier

variable [DecidableEq G]

lemma mem_carrier {P : GAP G} {x : G} : x ∈ P.carrier ↔ ∃ c ≤ P.bound, P.eval c = x := by
  simp [carrier]

lemma eval_mem_carrier (P : GAP G) {c : G →₀ ℕ} (hc : c ≤ P.bound) : P.eval c ∈ P.carrier :=
  mem_carrier.2 ⟨c, hc, rfl⟩

lemma origin_mem (P : GAP G) : P.origin ∈ P.carrier := by
  simpa using P.eval_mem_carrier (c := 0) zero_le

lemma nonempty (P : GAP G) : P.carrier.Nonempty :=
  ⟨_, P.origin_mem⟩

/-- The points of `P + Q` are the sums of a point of `P` and a point of `Q`. -/
lemma carrier_add (P Q : GAP G) : (P + Q).carrier = P.carrier + Q.carrier := by
  ext x
  simp only [mem_carrier, Finset.mem_add, bound_add]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := exists_add_eq_of_le_add hc
    exact ⟨_, ⟨c₁, hc₁, rfl⟩, _, ⟨c₂, hc₂, rfl⟩, (eval_add P Q c₁ c₂).symm⟩
  · rintro ⟨_, ⟨c₁, hc₁, rfl⟩, _, ⟨c₂, hc₂, rfl⟩, rfl⟩
    exact ⟨c₁ + c₂, add_le_add hc₁ hc₂, eval_add P Q c₁ c₂⟩

end Carrier

lemma dim_add_le (P Q : GAP G) : (P + Q).dim ≤ P.dim + Q.dim := by
  classical
  exact (Finset.card_le_card Finsupp.support_add).trans (Finset.card_union_le _ _)

/-! ## Progressions with numbered steps -/

/-- The GAP with the given origin, numbered steps `step i` and lengths `length i`, whose bound is
`∑ i, Finsupp.single (step i) (length i - 1)`. Equal steps are merged, and steps of length `1` do
not contribute. -/
def ofSteps {d : ℕ} (origin : G) (step : Fin d → G) (length : Fin d → ℕ) : GAP G :=
  ⟨origin, ∑ i, Finsupp.single (step i) (length i - 1)⟩

section OfSteps

variable {d : ℕ} {origin : G} {step : Fin d → G} {length : Fin d → ℕ}

lemma carrier_ofSteps [DecidableEq G] (hl : ∀ i, 0 < length i) :
    (ofSteps origin step length).carrier = Finset.univ.image (gapMap origin step length) := by
  ext x
  simp only [mem_carrier, ofSteps, le_sum_single_iff, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨fun i ↦ ⟨w i, by grind [hw i, hl i]⟩, ?_⟩
    rw [eval_sum_single]
    rfl
  · rintro ⟨w, rfl⟩
    refine ⟨_, ⟨fun i ↦ w i, fun i ↦ by grind [(w i).isLt], rfl⟩, ?_⟩
    rw [eval_sum_single]
    rfl

lemma proper_ofSteps (hl : ∀ i, 0 < length i) (h : Function.Injective (gapMap origin step length)) :
    (ofSteps origin step length).Proper := by
  intro c hc c' hc' he
  obtain ⟨w, hw, rfl⟩ := le_sum_single_iff.1 (Set.mem_Iic.1 hc)
  obtain ⟨w', hw', rfl⟩ := le_sum_single_iff.1 (Set.mem_Iic.1 hc')
  rw [eval_sum_single, eval_sum_single] at he
  obtain rfl : w = w' := by
    funext i
    simpa [Fin.ext_iff] using congr_fun (@h (fun i ↦ ⟨w i, by grind [hw i, hl i]⟩)
      (fun i ↦ ⟨w' i, by grind [hw' i, hl i]⟩) he) i
  rfl

/-- A GAP with distinct numbered steps is proper if and only if its points
`origin + ∑ i, w i • step i` with `w i < length i` are distinct. -/
lemma proper_ofSteps_iff (hs : Function.Injective step) (hl : ∀ i, 0 < length i) :
    (ofSteps origin step length).Proper ↔ Function.Injective (gapMap origin step length) := by
  classical
  refine ⟨?_, proper_ofSteps hl⟩
  intro h w₁ w₂ hw
  have heq := h (le_sum_single_iff.2 ⟨fun i ↦ w₁ i, fun i ↦ by grind [(w₁ i).isLt], rfl⟩)
    (le_sum_single_iff.2 ⟨fun i ↦ w₂ i, fun i ↦ by grind [(w₂ i).isLt], rfl⟩)
    (by rwa [eval_sum_single, eval_sum_single])
  funext i
  exact Fin.ext (by simpa [Finsupp.finsetSum_apply, Finsupp.single_apply, hs.eq_iff] using
    DFunLike.congr_fun heq (step i))

lemma dim_ofSteps_le : (ofSteps origin step length).dim ≤ d := by
  classical
  refine (Finset.card_le_card (t := Finset.univ.image step)
    (Finsupp.support_finsetSum.trans ?_)).trans (Finset.card_image_le.trans_eq (Finset.card_fin d))
  intro v hv
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hv
  exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, (Finset.mem_singleton.1
    (Finsupp.support_single_subset hi)).symm⟩

/-- A GAP with `d` distinct numbered steps, all of length at least `2`, has dimension `d`. -/
lemma dim_ofSteps (hs : Function.Injective step) (hl : ∀ i, 1 < length i) :
    (ofSteps origin step length).dim = d := by
  classical
  refine (congrArg Finset.card ?_).trans ((Finset.card_image_of_injective _ hs).trans
    (Finset.card_fin d))
  ext v
  simp only [ofSteps, Finsupp.mem_support_iff, Finsupp.finsetSum_apply, Finsupp.single_apply,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro h
    by_contra! hv
    apply h
    apply Finset.sum_eq_zero
    intro i _
    simp [hv i]
  · rintro ⟨j, rfl⟩
    simp only [hs.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    grind [hl j]

lemma card_carrier_ofSteps_le [DecidableEq G] (hl : ∀ i, 0 < length i) :
    (ofSteps origin step length).carrier.card ≤ ∏ i, length i := by
  rw [carrier_ofSteps hl]
  exact Finset.card_image_le.trans (by simp)

end OfSteps

/-- The steps of a GAP, numbered: the elements `v` with `P.bound v ≠ 0`. -/
def step (P : GAP G) (i : Fin P.dim) : G := P.bound.support.equivFin.symm i

/-- The length `P.bound v + 1` of the `i`-th step `v` of a GAP. -/
def length (P : GAP G) (i : Fin P.dim) : ℕ := P.bound (P.step i) + 1

lemma step_injective (P : GAP G) : Function.Injective P.step :=
  Subtype.val_injective.comp P.bound.support.equivFin.symm.injective

lemma step_mem_support (P : GAP G) (i : Fin P.dim) : P.step i ∈ P.bound.support :=
  (P.bound.support.equivFin.symm i).prop

lemma one_lt_length (P : GAP G) (i : Fin P.dim) : 1 < P.length i :=
  Nat.succ_lt_succ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 (P.step_mem_support i)))

lemma length_pos (P : GAP G) (i : Fin P.dim) : 0 < P.length i :=
  Nat.succ_pos _

lemma bound_ofSteps_step_length (P : GAP G) (origin : G) :
    (ofSteps origin P.step P.length).bound = P.bound := by
  simp only [ofSteps, length, Nat.add_sub_cancel]
  conv_rhs => rw [← Finsupp.sum_single P.bound]
  rw [Finsupp.sum, ← Finset.sum_coe_sort (s := P.bound.support),
    ← P.bound.support.equivFin.symm.sum_comp]
  rfl

lemma ofSteps_step_length (P : GAP G) : ofSteps P.origin P.step P.length = P :=
  ext rfl (P.bound_ofSteps_step_length P.origin)

lemma carrier_eq [DecidableEq G] (P : GAP G) :
    P.carrier = Finset.univ.image (gapMap P.origin P.step P.length) := by
  conv_lhs => rw [← P.ofSteps_step_length]
  exact carrier_ofSteps P.length_pos

/-- A GAP is proper if and only if its points `P.origin + ∑ i, w i • P.step i` with
`w i < P.length i` are distinct. -/
lemma proper_iff_injective (P : GAP G) :
    P.Proper ↔ Function.Injective (gapMap P.origin P.step P.length) := by
  conv_lhs => rw [← P.ofSteps_step_length]
  exact proper_ofSteps_iff P.step_injective P.length_pos

/-- An element `x` lies in a GAP `P` if and only if `x = P.origin + ∑ i, c i • P.step i` for some
natural numbers `c i < P.length i`. -/
lemma mem_carrier_iff [DecidableEq G] (P : GAP G) {x : G} :
    x ∈ P.carrier ↔ ∃ c : Fin P.dim → ℕ, (∀ i, c i < P.length i) ∧
      P.origin + ∑ i, c i • P.step i = x := by
  rw [P.carrier_eq]
  exact mem_image_gapMap_iff

/-! ## The size of a progression -/

/-- The number `∏ v ∈ P.bound.support, (P.bound v + 1)` of coefficient vectors `c ≤ P.bound` of a
GAP. -/
def size (P : GAP G) : ℕ := ∏ v ∈ P.bound.support, (P.bound v + 1)

lemma size_eq_card_Iic [DecidableEq G] (P : GAP G) : P.size = (Finset.Iic P.bound).card := by
  simp [size, Finsupp.card_Iic]

lemma size_eq_prod_length (P : GAP G) : P.size = ∏ i, P.length i := by
  rw [size, ← Finset.prod_coe_sort (s := P.bound.support),
    ← P.bound.support.equivFin.symm.prod_comp]
  rfl

section Size

variable [DecidableEq G]

lemma card_le_size (P : GAP G) : P.carrier.card ≤ P.size :=
  Finset.card_image_le.trans_eq P.size_eq_card_Iic.symm

/-- A GAP `P` is proper if and only if it has `P.size` elements. This is the definition of
properness of Chang and of Green. -/
lemma proper_iff_card_eq_size (P : GAP G) : P.Proper ↔ P.carrier.card = P.size := by
  rw [size_eq_card_Iic, carrier, Finset.card_image_iff, Finset.coe_Iic]
  rfl

lemma card_eq_size {P : GAP G} (h : P.Proper) : P.carrier.card = P.size :=
  P.proper_iff_card_eq_size.1 h

/-- A GAP `P` is proper if and only if it has `∏ i, P.length i` elements. -/
lemma proper_iff_card_eq_prod_length (P : GAP G) : P.Proper ↔ P.carrier.card = ∏ i, P.length i := by
  rw [proper_iff_card_eq_size, size_eq_prod_length]

lemma card_eq_prod_length (P : GAP G) (h : P.Proper) : P.carrier.card = ∏ i, P.length i :=
  P.proper_iff_card_eq_prod_length.1 h

lemma card_le_prod_length (P : GAP G) : P.carrier.card ≤ ∏ i, P.length i :=
  P.size_eq_prod_length ▸ P.card_le_size

end Size

lemma size_add_le (P Q : GAP G) : (P + Q).size ≤ P.size * Q.size := by
  classical
  rw [size_eq_card_Iic, size_eq_card_Iic, size_eq_card_Iic]
  refine (Finset.card_le_card ?_).trans Finset.card_add_le
  intro c hc
  obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := exists_add_eq_of_le_add (Finset.mem_Iic.1 hc)
  exact Finset.add_mem_add (Finset.mem_Iic.2 hc₁) (Finset.mem_Iic.2 hc₂)

/-- The sum of a GAP `P` and a GAP with the same bound has at most `2 ^ P.dim` times as many
coefficient vectors as `P`. -/
lemma size_add_le_of_bound_eq {P Q : GAP G} (h : Q.bound = P.bound) :
    (P + Q).size ≤ 2 ^ P.dim * P.size := by
  classical
  rw [size, bound_add, h, Finsupp.support_add_eq_union, Finset.union_self, dim, size,
    ← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  intro v _
  simp only [Finsupp.add_apply]
  grind

/-! ## Two-proper progressions -/

/-- The sum of a GAP `P` and a GAP with the same bound is the GAP with the steps of `P` and the
lengths `2 * P.length i - 1`. -/
lemma add_eq_ofSteps {P Q : GAP G} (h : Q.bound = P.bound) :
    P + Q = ofSteps (P.origin + Q.origin) P.step fun i ↦ 2 * P.length i - 1 := by
  refine ext rfl ?_
  rw [bound_add, h, ← P.bound_ofSteps_step_length 0]
  simp only [ofSteps, ← Finset.sum_add_distrib, ← Finsupp.single_add]
  congr with i
  grind [P.length_pos i]

/-- A GAP is `2`-proper if and only if the points `2 • P.origin + ∑ i, w i • P.step i` with
`w i < 2 * P.length i - 1` are distinct. -/
lemma twoProper_iff_injective (P : GAP G) : P.TwoProper ↔
    Function.Injective (gapMap (P.origin + P.origin) P.step fun i ↦ 2 * P.length i - 1) := by
  rw [TwoProper, add_eq_ofSteps rfl]
  exact proper_ofSteps_iff P.step_injective fun i ↦ by grind [P.length_pos i]

lemma TwoProper.proper {P : GAP G} (h : P.TwoProper) : P.Proper := by
  intro c hc c' hc' he
  refine h (le_add_right (Set.mem_Iic.1 hc)) (le_add_right (Set.mem_Iic.1 hc')) ?_
  rw [← add_zero c, ← add_zero c', eval_add, eval_add, he]

/-! ## Coefficients -/

section CoefficientBox

variable (P : GAP G)

/-- The coefficient box of a GAP, embedded in integer vectors. -/
def box : Finset (Fin P.dim → ℤ) :=
  Finset.univ.image fun (w : (i : Fin P.dim) → Fin (P.length i)) i ↦ (w i : ℤ)

lemma card_box : P.box.card = ∏ i, P.length i := by
  rw [box, Finset.card_image_of_injective]
  · simp [Fintype.card_pi]
  · intro w₁ w₂ hw
    ext i
    simpa using congr_fun hw i

/-- Add two coefficient vectors of a GAP. The sums have coordinates `w i < 2 * P.length i - 1`. -/
def sumCoefficients (w₁ w₂ : (i : Fin P.dim) → Fin (P.length i)) :
    (i : Fin P.dim) → Fin (2 * P.length i - 1) :=
  fun i ↦ ⟨(w₁ i : ℕ) + w₂ i, by grind⟩

lemma gapMap_add_eq (w₁ w₂ : (i : Fin P.dim) → Fin (P.length i)) :
    gapMap P.origin P.step P.length w₁ + gapMap P.origin P.step P.length w₂ =
      gapMap (P.origin + P.origin) P.step (fun i ↦ 2 * P.length i - 1)
        (P.sumCoefficients w₁ w₂) := by
  simp only [gapMap, sumCoefficients, Fin.val_mk]
  simp_rw [add_nsmul]
  rw [Finset.sum_add_distrib]
  ac_rfl

/-- Every coefficient vector with `w i < 2 * P.length i - 1` is the sum of two coefficient vectors
of the GAP. -/
lemma exists_sumCoefficients_eq (u : (i : Fin P.dim) → Fin (2 * P.length i - 1)) :
    ∃ w₁ w₂, P.sumCoefficients w₁ w₂ = u := by
  refine ⟨fun i ↦ ⟨min (u i : ℕ) (P.length i - 1), by grind [P.length_pos i]⟩,
    fun i ↦ ⟨u i - min (u i : ℕ) (P.length i - 1), by grind⟩, ?_⟩
  ext i
  simp [sumCoefficients]

lemma sumCoefficients_eq_iff {w₁ w₂ w₃ w₄ : (i : Fin P.dim) → Fin (P.length i)} :
    P.sumCoefficients w₁ w₂ = P.sumCoefficients w₃ w₄ ↔
      (fun i ↦ (w₁ i : ℤ) + w₂ i) = fun i ↦ (w₃ i : ℤ) + w₄ i := by
  simp only [funext_iff, Fin.ext_iff, sumCoefficients]
  norm_cast

end CoefficientBox

section Coefficients

variable [DecidableEq G] (P : GAP G)

/-- Coefficients `w i < P.length i` of an element `x` of a GAP, so that
`x = P.origin + ∑ i, w i • P.step i`. They are all `0` when `x` does not lie in the GAP. -/
def coeff (x : G) : (i : Fin P.dim) → Fin (P.length i) :=
  if hx : x ∈ P.carrier then (Finset.mem_image.1 (P.carrier_eq ▸ hx)).choose
  else fun i ↦ ⟨0, P.length_pos i⟩

lemma gapMap_coeff {x : G} (hx : x ∈ P.carrier) :
    gapMap P.origin P.step P.length (P.coeff x) = x := by
  obtain ⟨-, h⟩ := (Finset.mem_image.1 (P.carrier_eq ▸ hx)).choose_spec
  rwa [coeff, dite_eq_left hx]

/-- The coefficients `P.coeff x` of `x`, as an integer vector. -/
def coordinateMap (x : G) : Fin P.dim → ℤ :=
  fun i ↦ P.coeff x i

lemma coordinateMap_mem_box (x : G) : P.coordinateMap x ∈ P.box :=
  Finset.mem_image_of_mem _ (Finset.mem_univ (P.coeff x))

lemma gapMap_mem_carrier (w : (i : Fin P.dim) → Fin (P.length i)) :
    gapMap P.origin P.step P.length w ∈ P.carrier := by
  simp [P.carrier_eq]

lemma Proper.coeff_gapMap {P : GAP G} (h : P.Proper) (w : (i : Fin P.dim) → Fin (P.length i)) :
    P.coeff (gapMap P.origin P.step P.length w) = w :=
  P.proper_iff_injective.1 h (P.gapMap_coeff (P.gapMap_mem_carrier w))

lemma Proper.coordinateMap_gapMap {P : GAP G} (h : P.Proper)
    (w : (i : Fin P.dim) → Fin (P.length i)) :
    P.coordinateMap (gapMap P.origin P.step P.length w) = fun i ↦ (w i : ℤ) :=
  funext fun i ↦ by simp [coordinateMap, h.coeff_gapMap]

lemma coordinateMap_injOn : Set.InjOn P.coordinateMap P.carrier := by
  intro x hx y hy hxy
  rw [← P.gapMap_coeff hx, ← P.gapMap_coeff hy]
  congr 1
  ext i
  simpa [coordinateMap] using congr_fun hxy i

lemma coordinateMap_bijOn (h : P.Proper) :
    Set.BijOn P.coordinateMap P.carrier P.box := by
  refine ⟨fun x _ ↦ P.coordinateMap_mem_box x, P.coordinateMap_injOn, ?_⟩
  intro y hy
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hy
  exact ⟨gapMap P.origin P.step P.length w, P.gapMap_mem_carrier w, h.coordinateMap_gapMap w⟩

/-- The coordinate map of a GAP is a bijection onto its box if and only if the GAP is proper. -/
lemma coordinateMap_bijOn_iff : Set.BijOn P.coordinateMap P.carrier P.box ↔ P.Proper := by
  refine ⟨?_, P.coordinateMap_bijOn⟩
  intro h
  rw [proper_iff_card_eq_prod_length, ← card_box]
  exact Set.BijOn.finsetCard_eq _ h

lemma coordinateMap_add_eq_iff {P : GAP G} (h : P.TwoProper) {a b c d : G}
    (ha : a ∈ P.carrier) (hb : b ∈ P.carrier) (hc : c ∈ P.carrier)
    (hd : d ∈ P.carrier) :
    P.coordinateMap a + P.coordinateMap b = P.coordinateMap c + P.coordinateMap d ↔
      a + b = c + d := by
  conv_rhs => rw [← P.gapMap_coeff ha, ← P.gapMap_coeff hb, ← P.gapMap_coeff hc,
    ← P.gapMap_coeff hd, P.gapMap_add_eq, P.gapMap_add_eq,
    (P.twoProper_iff_injective.1 h).eq_iff, sumCoefficients_eq_iff]
  rfl

/-- The coordinate map of a GAP `P` is a Freiman `2`-isomorphism onto its box if and only if `P` is
`2`-proper. The first condition says that `P` is an `F₂`-progression in the sense of Bilu. -/
lemma coordinateMap_isAddFreimanIso_iff :
    IsAddFreimanIso 2 P.carrier P.box P.coordinateMap ↔ P.TwoProper := by
  constructor
  · intro h
    have hP := P.coordinateMap_bijOn_iff.1 h.bijOn
    rw [twoProper_iff_injective]
    intro u₁ u₂ hu
    obtain ⟨w₁, w₂, rfl⟩ := P.exists_sumCoefficients_eq u₁
    obtain ⟨w₃, w₄, rfl⟩ := P.exists_sumCoefficients_eq u₂
    rw [← P.gapMap_add_eq, ← P.gapMap_add_eq, ← h.add_eq_add (P.gapMap_mem_carrier w₁)
      (P.gapMap_mem_carrier w₂) (P.gapMap_mem_carrier w₃) (P.gapMap_mem_carrier w₄)] at hu
    rw [hP.coordinateMap_gapMap, hP.coordinateMap_gapMap, hP.coordinateMap_gapMap,
      hP.coordinateMap_gapMap] at hu
    exact P.sumCoefficients_eq_iff.2 hu
  · intro h
    exact isAddFreimanIso_two.mpr ⟨P.coordinateMap_bijOn h.proper,
      fun _ ha _ hb _ hc _ hd ↦ coordinateMap_add_eq_iff h ha hb hc hd⟩

lemma coordinateMap_isAddFreimanIso {P : GAP G} (h : P.TwoProper) :
    IsAddFreimanIso 2 P.carrier P.box P.coordinateMap :=
  P.coordinateMap_isAddFreimanIso_iff.2 h

end Coefficients

/-! ## Images and translates -/

/-- The image of a GAP under an additive homomorphism `f`: the GAP with origin `f P.origin`, steps
`f (P.step i)` and the same lengths. -/
def map {H : Type*} [AddCommMonoid H] (f : G →+ H) (P : GAP G) : GAP H :=
  ofSteps (f P.origin) (fun i ↦ f (P.step i)) P.length

lemma carrier_map [DecidableEq G] {H : Type*} [DecidableEq H] [AddCommMonoid H] (f : G →+ H)
    (P : GAP G) : (P.map f).carrier = P.carrier.image f := by
  rw [map, carrier_ofSteps P.length_pos, P.carrier_eq, Finset.image_image]
  congr with w
  simp [gapMap, map_sum]

lemma dim_map_le {H : Type*} [AddCommMonoid H] (f : G →+ H) (P : GAP G) :
    (P.map f).dim ≤ P.dim :=
  dim_ofSteps_le

lemma card_map_le [DecidableEq G] {H : Type*} [DecidableEq H] [AddCommMonoid H] (f : G →+ H)
    (P : GAP G) : (P.map f).carrier.card ≤ P.carrier.card := by
  rw [carrier_map]
  exact Finset.card_image_le

/-- Translate a GAP by a constant. -/
def shift (P : GAP G) (c : G) : GAP G := ⟨P.origin + c, P.bound⟩

lemma carrier_shift [DecidableEq G] (P : GAP G) (c : G) :
    (P.shift c).carrier = P.carrier.image (· + c) := by
  rw [carrier, carrier, Finset.image_image]
  congr 1
  funext x
  simp [shift, eval, add_right_comm]

@[simp] lemma dim_shift (P : GAP G) (c : G) : (P.shift c).dim = P.dim := rfl

end GAP

/-! ## The step homomorphism and the symmetric coefficient box

Both are defined for a GAP in an abelian group, where coefficients may be taken in `ℤ`.
-/

section Steps

variable {G : Type*} [AddCommGroup G]

/-- The homomorphism `(Fin d → ℤ) →+ G` attached to a family of steps: the integer linear
combination `Fintype.linearCombination ℤ step`. -/
def stepsHom {d : ℕ} (step : Fin d → G) : (Fin d → ℤ) →+ G :=
  (Fintype.linearCombination ℤ step).toAddMonoidHom

lemma stepsHom_apply {d : ℕ} (step : Fin d → G) (v : Fin d → ℤ) :
    stepsHom step v = ∑ i, v i • step i :=
  Fintype.linearCombination_apply ℤ step v

/-- On nonnegative coefficients the step homomorphism agrees with the `ℕ`-linear combination. -/
lemma stepsHom_natCast {d : ℕ} (step : Fin d → G) (w : (i : Fin d) → ℕ) :
    stepsHom step (fun i ↦ (w i : ℤ)) = ∑ i, w i • step i := by
  simp [stepsHom_apply]

end Steps

variable {G : Type*} [AddCommGroup G]

/-- The homomorphism `(Fin P.dim → ℤ) →+ G` given by the steps of a GAP. -/
def stepHom (P : GAP G) : (Fin P.dim → ℤ) →+ G := stepsHom P.step

lemma stepHom_coordinateMap [DecidableEq G] (P : GAP G) {x : G} (hx : x ∈ P.carrier) :
    stepHom P (P.coordinateMap x) = x - P.origin := by
  rw [eq_sub_iff_add_eq, add_comm]
  simpa [gapMap, stepHom, stepsHom_apply, GAP.coordinateMap] using P.gapMap_coeff hx

/-- The symmetric box of differences of coefficient vectors of a GAP. -/
def symBox (P : GAP G) : Finset (Fin P.dim → ℤ) :=
  Finset.Icc (fun i ↦ -((P.length i : ℤ) - 1)) fun i ↦ (P.length i : ℤ) - 1

lemma mem_symBox {P : GAP G} {v : Fin P.dim → ℤ} :
    v ∈ symBox P ↔ ∀ i, |v i| < P.length i := by
  simp only [symBox, Finset.mem_Icc, Pi.le_def, abs_lt, ← forall_and]
  apply forall_congr'
  intro i
  grind

end

end ChangFreimanRuzsa
