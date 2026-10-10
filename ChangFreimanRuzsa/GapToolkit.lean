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
(GAPs) and their interaction with Freiman isomorphisms. It is used for the formalization of
Appendix A of Campos–Dahia–Marciano, which proves a version of Chang's theorem for prime cyclic
groups.

The main pieces are:

- `GAP G`: a (not necessarily proper) GAP with ℕ-coefficients `0 ≤ wᵢ < ℓᵢ`;
- `GAP.Proper` and `GAP.TwoProper`: injectivity on the carrier and on the doubled box;
- the coordinate map of a 2-proper GAP is a Freiman 2-isomorphism onto its box in ℤᵈ;
- affine images of GAPs, including the linear map ℤᵈ → ℤ/q used in Appendix A;
- a cardinality bound `|P - P| ≤ 2ᵈ |P|` for 2-proper GAPs.

All results are stated in a single ambient `noncomputable section` because the coordinate map is
defined via choice.
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
  exact Classical.choose_spec (show ∃ w, gapMap P.origin P.step P.length w = x from by
    simpa [P.carrier_eq] using hx)

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
  have hcoeff : P.coefficientsFin x = P.coefficientsFin y := by
    funext i
    apply Fin.ext
    have hi := congr_fun hxy i
    change (P.coefficientsFin x i : ℤ) = (P.coefficientsFin y i : ℤ) at hi
    exact_mod_cast hi
  rw [← P.coefficientsFin_spec hx, hcoeff, P.coefficientsFin_spec hy]

lemma coordinateMap_bijOn (h : P.Proper) :
    Set.BijOn P.coordinateMap P.carrier P.box := by
  refine ⟨?_, P.coordinateMap_injective_on h, ?_⟩
  · intro x hx
    exact P.coordinateMap_mem_box hx
  · intro y hy
    change y ∈ P.box at hy
    rw [box, Finset.mem_image] at hy
    obtain ⟨w, _, hwy⟩ := hy
    subst y
    let x := gapMap P.origin P.step P.length w
    have hx : x ∈ P.carrier := by
      rw [P.carrier_eq, Finset.mem_image]
      exact ⟨w, Finset.mem_univ _, by simp [x]⟩
    refine ⟨x, hx, ?_⟩
    unfold coordinateMap
    rw [P.coefficientsFin_eq_of_proper h hx (w := w) (by simp [x])]

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
  constructor
  · intro h
    funext i
    have hi := congr_fun h i
    have hinat := congr_arg Fin.val hi
    exact_mod_cast hinat
  · intro h
    funext i
    apply Fin.ext
    have hi := congr_fun h i
    exact_mod_cast hi

lemma coordinateMap_add_eq_iff (h : P.TwoProper) {a b c d : G}
    (ha : a ∈ P.carrier) (hb : b ∈ P.carrier) (hc : c ∈ P.carrier)
    (hd : d ∈ P.carrier) :
    P.coordinateMap a + P.coordinateMap b = P.coordinateMap c + P.coordinateMap d ↔
      a + b = c + d := by
  rw [show P.coordinateMap a + P.coordinateMap b = P.coordinateMap c + P.coordinateMap d ↔
      (fun i ↦ (P.coefficientsFin a i : ℤ) + P.coefficientsFin b i) =
        fun i ↦ (P.coefficientsFin c i : ℤ) + P.coefficientsFin d i by rfl,
    ← P.sumCoefficients_eq_iff]
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
  let u₁ : (i : Fin P.dim) → Fin (2 * P.length i) :=
    fun i ↦ ⟨2 * (w₁ i : ℕ), by omega⟩
  let u₂ : (i : Fin P.dim) → Fin (2 * P.length i) :=
    fun i ↦ ⟨2 * (w₂ i : ℕ), by omega⟩
  have key : gapMap (2 • P.origin) P.step (fun i ↦ 2 * P.length i) u₁ =
      gapMap (2 • P.origin) P.step (fun i ↦ 2 * P.length i) u₂ := by
    simp only [gapMap, u₁, u₂]
    have h1 : ∑ i : Fin P.dim, (2 * (w₁ i : ℕ)) • P.step i =
        2 • ∑ i : Fin P.dim, (w₁ i : ℕ) • P.step i := by
      simp_rw [two_mul, add_nsmul]
      rw [Finset.sum_add_distrib, ← Finset.sum_nsmul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [two_nsmul]
    have h2 : ∑ i : Fin P.dim, (2 * (w₂ i : ℕ)) • P.step i =
        2 • ∑ i : Fin P.dim, (w₂ i : ℕ) • P.step i := by
      simp_rw [two_mul, add_nsmul]
      rw [Finset.sum_add_distrib, ← Finset.sum_nsmul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [two_nsmul]
    rw [h1, h2]
    rw [← nsmul_add, ← nsmul_add]
    change 2 • gapMap P.origin P.step P.length w₁ =
      2 • gapMap P.origin P.step P.length w₂
    rw [heq]
  have hu : u₁ = u₂ := h key
  funext i
  apply Fin.ext
  have hi := congr_arg (fun w ↦ (w i : ℕ)) hu
  dsimp [u₁, u₂] at hi
  omega

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
  apply Finset.image_nonempty.mpr
  let w : (i : Fin P.dim) → Fin (P.length i) := fun i ↦ ⟨0, P.length_pos i⟩
  exact ⟨w, Finset.mem_univ w⟩

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
    (f : G →+ H) : (P.map f).carrier.card ≤ P.carrier.card := by
  exact Finset.card_image_le

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

Both are defined for a GAP in an ambient abelian group, where coefficients may be taken in `ℤ`.
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
  rw [stepsHom_apply]
  exact Finset.sum_congr rfl fun i _ ↦ natCast_zsmul (step i) (w i)

end Steps

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-- The homomorphism `ℤᵈ →+ G` given by the steps of a GAP. -/
def stepHom (P : GAP G) : (Fin P.dim → ℤ) →+ G := stepsHom P.step

lemma stepHom_coordinateMap (P : GAP G) {x : G} (hx : x ∈ P.carrier) :
    stepHom P (P.coordinateMap x) = x - P.origin := by
  rw [eq_sub_iff_add_eq, add_comm]
  simpa only [gapMap, stepHom, stepsHom, GAP.coordinateMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    natCast_zsmul] using P.coefficientsFin_spec hx

/-- The symmetric box of differences of coefficient vectors of a GAP. -/
def symBox (P : GAP G) : Finset (Fin P.dim → ℤ) :=
  Finset.Icc (fun i ↦ -((P.length i : ℤ) - 1)) fun i ↦ (P.length i : ℤ) - 1

lemma mem_symBox {P : GAP G} {v : Fin P.dim → ℤ} :
    v ∈ symBox P ↔ ∀ i, |v i| < (P.length i : ℤ) := by
  simp only [symBox, Finset.mem_Icc, Pi.le_def, abs_lt, ← forall_and]
  exact forall_congr' fun i ↦ by omega

end

end ChangFreimanRuzsa
