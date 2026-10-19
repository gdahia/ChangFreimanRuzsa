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

/-! # Generalized arithmetic progressions (proper and non-proper)

This file develops the basic theory of (not necessarily proper) generalized arithmetic progressions
(GAPs) and their interaction with Freiman isomorphisms.

## Main definitions

* `GAP G`: a GAP $\{x_0 + \sum_i w_i v_i : 0 \le w_i < \ell_i\}$ with natural coefficients.
* `GAP.Proper` and `GAP.TwoProper`: injectivity of the coefficient map on the box and on the
  doubled box.
* `GAP.coeff` and `GAP.coordinateMap`: coefficients of an element of a GAP.
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

/-- The points $x_0 + \sum_i w_i v_i$ with $0 \le w_i < \ell_i$ are the points
$x_0 + \sum_i c_i v_i$ with natural numbers $c_i < \ell_i$. -/
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

/-- A (not necessarily proper) generalized arithmetic progression with origin $x_0$, steps $v_i$
and lengths $\ell_i$. Its elements are the points $x_0 + \sum_i w_i v_i$ with natural numbers
$0 \le w_i < \ell_i$. -/
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

/-- An element $x$ lies in a GAP with origin $x_0$, steps $v_i$ and lengths $\ell_i$ if and only if
$x = x_0 + \sum_i c_i v_i$ for some natural numbers $c_i < \ell_i$. -/
lemma mem_carrier_iff {x : G} :
    x ∈ P.carrier ↔ ∃ c : Fin P.dim → ℕ, (∀ i, c i < P.length i) ∧
      P.origin + ∑ i, c i • P.step i = x := by
  rw [P.carrier_eq]
  exact mem_image_gapMap_iff

/-- Coefficients $0 \le w_i < \ell_i$ of an element $x$ of a GAP, so that
$x = x_0 + \sum_i w_i v_i$. They are all $0$ when $x$ does not lie in the GAP. -/
def coeff (x : G) : (i : Fin P.dim) → Fin (P.length i) :=
  if hx : x ∈ P.carrier then (Finset.mem_image.1 (P.carrier_eq ▸ hx)).choose
  else fun i ↦ ⟨0, P.length_pos i⟩

lemma gapMap_coeff {x : G} (hx : x ∈ P.carrier) :
    gapMap P.origin P.step P.length (P.coeff x) = x := by
  obtain ⟨-, h⟩ := (Finset.mem_image.1 (P.carrier_eq ▸ hx)).choose_spec
  rwa [coeff, dite_eq_left hx]

/-- A GAP is *proper* if every choice of coefficients gives a distinct element. -/
def Proper : Prop :=
  Function.Injective (gapMap P.origin P.step P.length)

/-- A GAP is *2-proper* if the doubled box is proper, i.e. `P + P` is proper. -/
def TwoProper : Prop :=
  Function.Injective (gapMap (2 • P.origin) P.step (fun i ↦ 2 * P.length i))

/-- The coefficient box of a GAP, embedded in integer vectors. -/
def box : Finset (Fin P.dim → ℤ) :=
  Finset.univ.image fun (w : (i : Fin P.dim) → Fin (P.length i)) i ↦ (w i : ℤ)

/-- The coefficients `P.coeff x` of $x$, as an integer vector. -/
def coordinateMap (x : G) : Fin P.dim → ℤ :=
  fun i ↦ P.coeff x i

lemma coordinateMap_mem_box (x : G) : P.coordinateMap x ∈ P.box :=
  Finset.mem_image_of_mem _ (Finset.mem_univ (P.coeff x))

lemma Proper.coeff_gapMap {P : GAP G} (h : P.Proper) (w : (i : Fin P.dim) → Fin (P.length i)) :
    P.coeff (gapMap P.origin P.step P.length w) = w :=
  h (P.gapMap_coeff (by simp [P.carrier_eq]))

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
  exact ⟨gapMap P.origin P.step P.length w, by simp [P.carrier_eq],
    funext fun i ↦ by simp [coordinateMap, h.coeff_gapMap]⟩

/-- Add two coefficient vectors inside the doubled box. -/
def sumCoefficients (w₁ w₂ : (i : Fin P.dim) → Fin (P.length i)) :
    (i : Fin P.dim) → Fin (2 * P.length i) :=
  fun i ↦ ⟨(w₁ i : ℕ) + w₂ i, by grind⟩

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
  conv_rhs => rw [← P.gapMap_coeff ha, ← P.gapMap_coeff hb, ← P.gapMap_coeff hc,
    ← P.gapMap_coeff hd, P.gapMap_add_eq, P.gapMap_add_eq, Function.Injective.eq_iff h,
    sumCoefficients_eq_iff]
  rfl

lemma TwoProper.proper {P : GAP G} (h : P.TwoProper) : P.Proper := by
  intro w₁ w₂ hw
  have hsum : P.sumCoefficients w₁ w₁ = P.sumCoefficients w₂ w₂ :=
    h (by simp [← P.gapMap_add_eq, hw])
  ext i
  grind [congr_fun (P.sumCoefficients_eq_iff.1 hsum) i]

lemma coordinateMap_isAddFreimanIso (h : P.TwoProper) :
    IsAddFreimanIso 2 P.carrier P.box P.coordinateMap :=
  isAddFreimanIso_two.mpr ⟨P.coordinateMap_bijOn h.proper,
    fun _ ha _ hb _ hc _ hd ↦ P.coordinateMap_add_eq_iff h ha hb hc hd⟩

lemma card_eq_prod_length (h : P.Proper) : P.carrier.card = ∏ i, P.length i := by
  rw [P.carrier_eq, Finset.card_image_of_injective _ h]
  simp [Fintype.card_pi]

lemma card_le_prod_length : P.carrier.card ≤ ∏ i, P.length i := by
  rw [P.carrier_eq]
  exact Finset.card_image_le.trans (by simp [Fintype.card_pi])

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
    congr with w
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
    congr 1 with w
    simp [gapMap, add_right_comm]

end GAP

/-! ## The step homomorphism and the symmetric coefficient box

Both are defined for a GAP in an abelian group, where coefficients may be taken in $\mathbb{Z}$.
-/

section Steps

variable {G : Type*} [AddCommGroup G]

/-- The homomorphism `ℤᵈ →+ G` attached to a family of steps: the integer linear combination
`Fintype.linearCombination ℤ step`. -/
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

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-- The homomorphism `ℤᵈ →+ G` given by the steps of a GAP. -/
def stepHom (P : GAP G) : (Fin P.dim → ℤ) →+ G := stepsHom P.step

lemma stepHom_coordinateMap (P : GAP G) {x : G} (hx : x ∈ P.carrier) :
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
