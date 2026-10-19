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
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Floor

/-! # Generalized arithmetic progressions (proper and non-proper)

This file develops the basic theory of (not necessarily proper) generalized arithmetic progressions
(GAPs) and their interaction with Freiman isomorphisms.

## Main definitions

* `GAP G`: a GAP $\{x_0 + \sum_i w_i v_i : 0 \le w_i < \ell_i\}$ with natural coefficients.
* `GAP.Proper` and `GAP.TwoProper`: injectivity of the coefficient map on the box and on the
  doubled box.
* `GAP.map` and `GAP.shift`: images of a GAP under additive homomorphisms and translations.
* `stepsHom`, `stepHom` and `symBox`: the homomorphism $\mathbb{Z}^d \to G$ given by the steps,
  and the symmetric box of differences of coefficient vectors.

## Main statements

* `GAP.coordinateMap_isAddFreimanIso`: the coordinate map of a 2-proper GAP is a Freiman
  2-isomorphism onto its box in $\mathbb{Z}^d$.
* `GAP.card_eq_prod_length`: a proper GAP has $\prod_i \ell_i$ elements.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open scoped Pointwise

noncomputable section

/-- A (not necessarily proper) generalized arithmetic progression.

The coefficients are `ℕ`-valued: every element is `origin + ∑ wᵢ • stepᵢ`
with `0 ≤ wᵢ < lengthᵢ`. -/
structure GAP (G : Type*) [DecidableEq G] [AddCommMonoid G] where
  dim : ℕ
  carrier : Finset G
  origin : G
  step : Fin dim → G
  length : Fin dim → ℕ
  length_pos : ∀ i, 0 < length i
  carrier_eq : carrier = Finset.univ.image (gapMap origin step length)

instance {G : Type*} [DecidableEq G] [AddCommMonoid G] : CoeOut (GAP G) (Finset G) where
  coe P := P.carrier

namespace GAP

variable {G : Type*} [DecidableEq G] [AddCommMonoid G] (P : GAP G)

/-- The coefficients of an element of a GAP as bounded `Fin` values. -/
noncomputable def coefficientsFin (x : G) : (i : Fin P.dim) → Fin (P.length i) :=
  if hx : x ∈ P.carrier then
    have : ∃ w, gapMap P.origin P.step P.length w = x := by
      simpa [P.carrier_eq] using hx
    Classical.choose this
  else fun _ ↦ ⟨0, P.length_pos _⟩

lemma coefficientsFin_spec {x : G} (hx : x ∈ P.carrier) :
    gapMap P.origin P.step P.length (P.coefficientsFin x) = x := by
  unfold coefficientsFin
  rw [dite_eq_left hx]
  generalize_proofs hw
  exact Classical.choose_spec hw

/-- A GAP is *proper* if every choice of coefficients gives a distinct element. -/
def Proper : Prop :=
  Function.Injective (gapMap P.origin P.step P.length)

/-- A GAP is *2-proper* if the doubled box is proper, i.e. `P + P` is proper. -/
def TwoProper : Prop :=
  Function.Injective (gapMap (2 • P.origin) P.step (fun i ↦ 2 * P.length i))

/-- The coefficient box of a GAP, embedded in integer vectors. -/
def box : Finset (Fin P.dim → ℤ) :=
  Finset.univ.image fun
    (w : (i : Fin P.dim) → Fin (P.length i)) i ↦
    (w i : ℤ)

/-- The total coordinate map associated with a GAP.

Its behavior outside the carrier is irrelevant. -/
noncomputable def coordinateMap (x : G) : Fin P.dim → ℤ :=
  fun i ↦ P.coefficientsFin x i

lemma coordinateMap_mem_box {x : G} (_hx : x ∈ P.carrier) :
    P.coordinateMap x ∈ P.box := by
  rw [box, Finset.mem_image]
  exact ⟨P.coefficientsFin x, Finset.mem_univ _, rfl⟩

lemma coefficientsFin_eq_of_proper (h : P.Proper) {x : G}
    {w : (i : Fin P.dim) → Fin (P.length i)}
    (hx : x ∈ P.carrier) (hw : gapMap P.origin P.step P.length w = x) :
    P.coefficientsFin x = w := by
  apply h
  rw [P.coefficientsFin_spec hx, hw]

lemma coordinateMap_injective_on (_h : P.Proper) :
    Set.InjOn P.coordinateMap P.carrier := by
  intro x hx y hy hxy
  rw [← P.coefficientsFin_spec hx, ← P.coefficientsFin_spec hy]
  congr 1
  ext i
  simpa [coordinateMap] using congr_fun hxy i

lemma coordinateMap_bijOn (h : P.Proper) :
    Set.BijOn P.coordinateMap P.carrier P.box := by
  refine ⟨fun x hx ↦ P.coordinateMap_mem_box hx, P.coordinateMap_injective_on h, ?_⟩
  intro y hy
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hy
  have hx : gapMap P.origin P.step P.length w ∈ P.carrier := by
    simp [P.carrier_eq]
  refine ⟨_, hx, ?_⟩
  unfold coordinateMap
  rw [P.coefficientsFin_eq_of_proper h hx rfl]

/-- Add two coefficient vectors inside the doubled box. -/
def sumCoefficients (w₁ w₂ : (i : Fin P.dim) → Fin (P.length i)) :
    (i : Fin P.dim) → Fin (2 * P.length i) :=
  fun i ↦ ⟨(w₁ i : ℕ) + w₂ i, by omega⟩

lemma gapMap_add_eq (w₁ w₂ : (i : Fin P.dim) → Fin (P.length i)) :
    gapMap P.origin P.step P.length w₁ + gapMap P.origin P.step P.length w₂ =
      gapMap (2 • P.origin) P.step (fun i ↦ 2 * P.length i)
        (P.sumCoefficients w₁ w₂) := by
  simp only [gapMap, sumCoefficients, Fin.val_mk]
  simp_rw [add_nsmul]
  rw [Finset.sum_add_distrib, two_nsmul]
  ac_rfl

lemma sumCoefficients_eq_iff {w₁ w₂ w₃ w₄ : (i : Fin P.dim) → Fin (P.length i)} :
    P.sumCoefficients w₁ w₂ = P.sumCoefficients w₃ w₄ ↔
      (fun i ↦ (w₁ i : ℤ) + w₂ i) = fun i ↦ (w₃ i : ℤ) + w₄ i := by
  simp only [funext_iff, Fin.ext_iff, sumCoefficients]
  norm_cast

lemma coordinateMap_add_eq_iff (h : P.TwoProper) {a b c d : G}
    (ha : a ∈ P.carrier) (hb : b ∈ P.carrier) (hc : c ∈ P.carrier)
    (hd : d ∈ P.carrier) :
    P.coordinateMap a + P.coordinateMap b = P.coordinateMap c + P.coordinateMap d ↔
      a + b = c + d := by
  change (fun i ↦ (P.coefficientsFin a i : ℤ) + P.coefficientsFin b i) =
      (fun i ↦ (P.coefficientsFin c i : ℤ) + P.coefficientsFin d i) ↔ a + b = c + d
  rw [← P.sumCoefficients_eq_iff]
  constructor
  · intro hsum
    rw [← P.coefficientsFin_spec ha, ← P.coefficientsFin_spec hb,
      ← P.coefficientsFin_spec hc, ← P.coefficientsFin_spec hd,
      P.gapMap_add_eq, P.gapMap_add_eq]
    exact congrArg _ hsum
  · intro hab
    apply h
    rw [← P.gapMap_add_eq, ← P.gapMap_add_eq,
      P.coefficientsFin_spec ha, P.coefficientsFin_spec hb,
      P.coefficientsFin_spec hc, P.coefficientsFin_spec hd]
    exact hab

lemma twoProper_proper (h : P.TwoProper) : P.Proper := by
  intro w₁ w₂ heq
  have hsum : P.sumCoefficients w₁ w₁ = P.sumCoefficients w₂ w₂ :=
    h (by simp [← P.gapMap_add_eq, heq])
  ext i
  have hi := congr_arg (fun w ↦ (w i : ℕ)) hsum
  simp only [sumCoefficients] at hi
  grind

lemma coordinateMap_isAddFreimanIso (h : P.TwoProper) :
    IsAddFreimanIso 2 P.carrier P.box P.coordinateMap := by
  refine isAddFreimanIso_two.mpr
    ⟨P.coordinateMap_bijOn (twoProper_proper P h), ?_⟩
  intro a ha b hb c hc d hd
  exact P.coordinateMap_add_eq_iff h ha hb hc hd

lemma card_eq_prod_length (h : P.Proper) : P.carrier.card = ∏ i, P.length i := by
  rw [P.carrier_eq, Finset.card_image_of_injective _ h]
  simp [Fintype.card_pi]

lemma card_le_prod_length : P.carrier.card ≤ ∏ i, P.length i := by
  rw [P.carrier_eq]
  refine Finset.card_image_le.trans (le_of_eq ?_)
  rw [Finset.card_univ, Fintype.card_pi]
  simp

lemma nonempty (P : GAP G) : P.carrier.Nonempty := by
  rw [P.carrier_eq]
  exact Finset.image_nonempty.mpr ⟨fun i ↦ ⟨0, P.length_pos i⟩, Finset.mem_univ _⟩

/-- The image of a GAP under an additive homomorphism. -/
def map {H : Type*} [DecidableEq H] [AddCommMonoid H] (f : G →+ H) (P : GAP G) : GAP H where
  dim := P.dim
  carrier := P.carrier.image f
  origin := f P.origin
  step := fun i ↦ f (P.step i)
  length := P.length
  length_pos := P.length_pos
  carrier_eq := by
    rw [P.carrier_eq, Finset.image_image]
    apply Finset.ext
    simp only [Finset.mem_image]
    intro x
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w, hw, ?_⟩
      simp [gapMap, map_sum]
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w, hw, ?_⟩
      simp [gapMap, map_sum]

lemma card_map_le {H : Type*} [DecidableEq H] [AddCommMonoid H]
    (f : G →+ H) : (P.map f).carrier.card ≤ P.carrier.card :=
  Finset.card_image_le

/-- Translate a GAP by a constant. -/
def shift (c : G) : GAP G where
  dim := P.dim
  carrier := P.carrier.image (· + c)
  origin := P.origin + c
  step := P.step
  length := P.length
  length_pos := P.length_pos
  carrier_eq := by
    rw [P.carrier_eq, Finset.image_image]
    apply Finset.ext
    simp only [Finset.mem_image]
    intro x
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w, hw, ?_⟩
      simp [gapMap]
      ac_rfl
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w, hw, ?_⟩
      simp [gapMap]
      ac_rfl

end GAP

/-! ## The step homomorphism and the symmetric coefficient box

Both are defined for a GAP in an abelian group, where coefficients may be taken in $\mathbb{Z}$.
-/

section Steps

variable {G : Type*} [AddCommGroup G]

/-- The homomorphism `ℤᵈ →+ G` attached to a family of steps. -/
def stepsHom {d : ℕ} (step : Fin d → G) : (Fin d → ℤ) →+ G where
  toFun v := ∑ i, v i • step i
  map_zero' := by simp
  map_add' a b := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ add_zsmul (step i) (a i) (b i)

lemma stepsHom_apply {d : ℕ} (step : Fin d → G) (v : Fin d → ℤ) :
    stepsHom step v = ∑ i, v i • step i := rfl

/-- On nonnegative coefficients the step homomorphism agrees with the `ℕ`-linear combination. -/
lemma stepsHom_natCast {d : ℕ} (step : Fin d → G) (w : (i : Fin d) → ℕ) :
    stepsHom step (fun i ↦ (w i : ℤ)) = ∑ i, w i • step i := by
  simp [stepsHom_apply]

end Steps

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-- The homomorphism `ℤᵈ →+ G` given by the steps of a GAP. -/
def stepHom (P : GAP G) : (Fin P.dim → ℤ) →+ G := stepsHom P.step

lemma stepHom_coordinateMap (P : GAP G) {x : G} (hx : x ∈ P.carrier) :
    stepHom P (P.coordinateMap x) = x - P.origin := by
  rw [eq_sub_iff_add_eq, add_comm]
  simpa [gapMap, stepHom, stepsHom, GAP.coordinateMap] using P.coefficientsFin_spec hx

/-- The symmetric box of differences of coefficient vectors of a GAP. -/
def symBox (P : GAP G) : Finset (Fin P.dim → ℤ) :=
  Finset.Icc (fun i ↦ -((P.length i : ℤ) - 1)) fun i ↦ (P.length i : ℤ) - 1

lemma mem_symBox {P : GAP G} {v : Fin P.dim → ℤ} :
    v ∈ symBox P ↔ ∀ i, |v i| < (P.length i : ℤ) := by
  simp only [symBox, Finset.mem_Icc, Pi.le_def, abs_lt, ← forall_and]
  apply forall_congr'
  intro i
  grind

end

end ChangFreimanRuzsa
