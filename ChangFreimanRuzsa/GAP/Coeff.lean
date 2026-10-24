/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GAP.Basic
public import Mathlib.Combinatorics.Additive.FreimanHom

/-!
# Coefficients of the elements of a generalized arithmetic progression

Every element `x` of a GAP `P` is `P.origin + ∑ i, w i • P.step i` for coefficients
`w i < P.length i`, which are unique when `P` is proper. This file chooses such coefficients and
relates properness and `2`-properness of `P` to the map that sends `x` to them.

## Main definitions

* `GAP.box`: the coefficient box of a GAP, as a set of integer vectors.
* `GAP.coeff` and `GAP.coordinateMap`: coefficients of an element of a GAP.

## Main statements

* `GAP.coordinateMap_bijOn_iff`: a GAP is proper if and only if its coordinate map is a bijection
  onto its box.
* `GAP.coordinateMap_isAddFreimanIso_iff`: the coordinate map of a GAP is a Freiman
  `2`-isomorphism onto its box in `ℤ ^ d` if and only if the GAP is `2`-proper.
* `stepHom_coordinateMap`: the step homomorphism sends the coordinates of `x` to `x - P.origin`.
-/

@[expose] public section

namespace ChangFreimanRuzsa

noncomputable section

namespace GAP

variable {G : Type*} [AddCommMonoid G]

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

lemma coordinateMap_add_eq_iff {P : GAP G} (h : (P + P).Proper) {a b c d : G}
    (ha : a ∈ P.carrier) (hb : b ∈ P.carrier) (hc : c ∈ P.carrier)
    (hd : d ∈ P.carrier) :
    P.coordinateMap a + P.coordinateMap b = P.coordinateMap c + P.coordinateMap d ↔
      a + b = c + d := by
  conv_rhs => rw [← P.gapMap_coeff ha, ← P.gapMap_coeff hb, ← P.gapMap_coeff hc,
    ← P.gapMap_coeff hd, P.gapMap_add_eq, P.gapMap_add_eq,
    (P.proper_add_self_iff_injective.1 h).eq_iff, sumCoefficients_eq_iff]
  rfl

/-- The coordinate map of a GAP `P` is a Freiman `2`-isomorphism onto its box if and only if `P` is
`2`-proper. The first condition says that `P` is an `F₂`-progression in the sense of Bilu. -/
lemma coordinateMap_isAddFreimanIso_iff :
    IsAddFreimanIso 2 P.carrier P.box P.coordinateMap ↔ (P + P).Proper := by
  constructor
  · intro h
    have hP := P.coordinateMap_bijOn_iff.1 h.bijOn
    rw [proper_add_self_iff_injective]
    intro u₁ u₂ hu
    obtain ⟨w₁, w₂, rfl⟩ := P.exists_sumCoefficients_eq u₁
    obtain ⟨w₃, w₄, rfl⟩ := P.exists_sumCoefficients_eq u₂
    rw [← P.gapMap_add_eq, ← P.gapMap_add_eq, ← h.add_eq_add (P.gapMap_mem_carrier w₁)
      (P.gapMap_mem_carrier w₂) (P.gapMap_mem_carrier w₃) (P.gapMap_mem_carrier w₄)] at hu
    rw [hP.coordinateMap_gapMap, hP.coordinateMap_gapMap, hP.coordinateMap_gapMap,
      hP.coordinateMap_gapMap] at hu
    exact P.sumCoefficients_eq_iff.2 hu
  · intro h
    exact isAddFreimanIso_two.mpr ⟨P.coordinateMap_bijOn h.of_add_self,
      fun _ ha _ hb _ hc _ hd ↦ coordinateMap_add_eq_iff h ha hb hc hd⟩

lemma coordinateMap_isAddFreimanIso {P : GAP G} (h : (P + P).Proper) :
    IsAddFreimanIso 2 P.carrier P.box P.coordinateMap :=
  P.coordinateMap_isAddFreimanIso_iff.2 h

end Coefficients

end GAP

variable {G : Type*} [AddCommGroup G]

lemma stepHom_coordinateMap [DecidableEq G] (P : GAP G) {x : G} (hx : x ∈ P.carrier) :
    stepHom P (P.coordinateMap x) = x - P.origin := by
  rw [eq_sub_iff_add_eq, add_comm]
  simpa [gapMap, stepHom, stepsHom_apply, GAP.coordinateMap] using P.gapMap_coeff hx

end

end ChangFreimanRuzsa
