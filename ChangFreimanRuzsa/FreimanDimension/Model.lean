/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GAP.Coeff
public import ChangFreimanRuzsa.GeometryOfNumbers.LatticeCoordinates
public import SumOfSetsInSeveralDimensions.FreimanDimension

/-!
# A Freiman model of a subset of a `2`-proper progression

Let `P` be a `2`-proper generalized arithmetic progression in an abelian group `G`, let
`X ⊆ P.toFinset` be finite and let `x₀ ∈ X`. Translate the coefficient vectors in `P` of the
elements of `X` so that the vector of `x₀` is the origin, and let `r` be the dimension of the real
span of the translated vectors. The map that sends `x ∈ X` to the coordinates of its translated
vector in a basis of the lattice of integer points of that span is a Freiman isomorphism of order
`2` from `X` onto a subset of `ℤ ^ r ⊆ ℚ ^ r` that contains the origin and spans `ℝ ^ r`. Hence
`r` is at most the Freiman dimension `freimanDim X`.

This is the model of Appendix A of Marcelo Campos, Gabriel Dahia and João Pedro Marciano, *On the
independence number of sparser random Cayley graphs*, J. London Math. Soc. 110 (2024).

## Main definitions

* `translatedCoords P X x₀`: the translated coefficient vectors of the elements of `X`.
* `modelDim P X x₀`: the dimension `r` of their real span.
* `modelFn P X x₀`: the map `G → ℚ ^ r`.

## Main statements

* `modelFn_isAddFreimanIso`: `modelFn P X x₀` is a Freiman isomorphism of order `2` from `X` onto
  its image.
* `finrank_direction_affineSpan_modelFn`: the image of `X` has affine dimension `r`.
* `modelDim_le_freimanDim`: `modelDim P X x₀ ≤ freimanDim X`.
-/

@[expose] public section

open Finset SumOfSetsInSeveralDimensions

namespace ChangFreimanRuzsa

noncomputable section

variable {G : Type*} [DecidableEq G] [AddCommGroup G] (P : GAP G) (X : Finset G) (x₀ : G)

/-- The coefficient vectors in `P` of the elements of `X`, translated by the coefficient vector of
`x₀`. -/
def translatedCoords : Finset (Fin P.dim → ℤ) :=
  X.image fun x ↦ P.coordinateMap x - P.coordinateMap x₀

/-- The dimension of the real span of `translatedCoords P X x₀`. -/
abbrev modelDim : ℕ := integerGeneratedRank (translatedCoords P X x₀)

/-- The map `G → ℚ ^ r` that sends `x` to the coordinates of its translated coefficient vector in
the basis `integerGeneratedLatticeBasis (translatedCoords P X x₀)`. -/
def modelFn (x : G) : Fin (modelDim P X x₀) → ℚ :=
  fun i ↦ latticeCoordinates (translatedCoords P X x₀) (P.coordinateMap x - P.coordinateMap x₀) i

variable {X}

lemma sub_coordinateMap_mem_translatedCoords {x : G} (hx : x ∈ X) :
    P.coordinateMap x - P.coordinateMap x₀ ∈ translatedCoords P X x₀ :=
  mem_image_of_mem _ hx

lemma sub_coordinateMap_mem_saturatedSpan {x : G} (hx : x ∈ X) :
    P.coordinateMap x - P.coordinateMap x₀ ∈ saturatedSpan (translatedCoords P X x₀) :=
  subset_saturatedSpan _ (sub_coordinateMap_mem_translatedCoords P x₀ hx)

variable {P x₀}

lemma coe_translatedCoords :
    (translatedCoords P X x₀ : Set (Fin P.dim → ℤ)) =
      (fun x ↦ P.coordinateMap x - P.coordinateMap x₀) '' X :=
  coe_image

private lemma intCast_add_intCast_eq_iff {r : ℕ} {a b c e : Fin r → ℤ} :
    ((fun i ↦ (a i : ℚ)) + fun i ↦ (b i : ℚ)) = ((fun i ↦ (c i : ℚ)) + fun i ↦ (e i : ℚ)) ↔
      a + b = c + e := by
  simp only [funext_iff, Pi.add_apply]
  norm_cast

/-- The model map is a Freiman isomorphism of order `2` from `X` onto its image. -/
lemma modelFn_isAddFreimanIso (hP : (P + P).Proper) (hXP : X ⊆ P.toFinset) :
    IsAddFreimanIso 2 (X : Set G)
      ((X.image (modelFn P X x₀) : Finset (Fin (modelDim P X x₀) → ℚ)) :
        Set (Fin (modelDim P X x₀) → ℚ)) (modelFn P X x₀) := by
  rw [coe_image]
  refine isAddFreimanIso_two.2 ⟨Set.InjOn.bijOn_image ?_, ?_⟩
  · intro a ha b hb hab
    apply P.coordinateMap_injOn (hXP ha) (hXP hb)
    apply sub_left_injective (b := P.coordinateMap x₀)
    apply latticeCoordinates_injOn _ (sub_coordinateMap_mem_saturatedSpan P x₀ ha)
      (sub_coordinateMap_mem_saturatedSpan P x₀ hb)
    ext i
    exact Int.cast_injective (α := ℚ) (congr_fun hab i)
  · intro a ha b hb c hc e he
    refine intCast_add_intCast_eq_iff.trans ?_
    rw [latticeCoordinates_add_eq_add_iff (sub_coordinateMap_mem_saturatedSpan P x₀ ha)
      (sub_coordinateMap_mem_saturatedSpan P x₀ hb) (sub_coordinateMap_mem_saturatedSpan P x₀ hc)
      (sub_coordinateMap_mem_saturatedSpan P x₀ he), sub_add_sub_comm, sub_add_sub_comm,
      sub_left_inj]
    exact P.coordinateMap_add_eq_iff hP (hXP ha) (hXP hb) (hXP hc) (hXP he)

/-- The image of `X` under the model map, viewed in `ℝ ^ r`, is the set of the real casts of the
lattice coordinates of the translated coefficient vectors. -/
private lemma coe_image_rationalVectorToReal_modelFn :
    (((X.image (modelFn P X x₀)).image rationalVectorToReal : Finset _) :
        Set (Fin (modelDim P X x₀) → ℝ)) =
      intVectorToReal '' (latticeCoordinates (translatedCoords P X x₀) ''
        (translatedCoords P X x₀ : Set (Fin P.dim → ℤ))) := by
  rw [coe_image, coe_image, coe_translatedCoords, Set.image_image, Set.image_image,
    Set.image_image]
  apply Set.image_congr
  intro x _
  ext i
  exact Rat.cast_intCast _

/-- A set that contains the origin and spans `V` has affine dimension `finrank ℝ V`. -/
private lemma finrank_direction_affineSpan_of_span_eq_top {V : Type*} [AddCommGroup V]
    [Module ℝ V] {T : Set V} (h₀ : 0 ∈ T) (hT : Submodule.span ℝ T = ⊤) :
    Module.finrank ℝ (affineSpan ℝ T).direction = Module.finrank ℝ V := by
  rw [affineSpan_eq_span_of_zero_mem (mem_affineSpan ℝ h₀), Submodule.toAffineSubspace_direction,
    hT, finrank_top]

/-- The image of `X` under the model map, viewed in `ℝ ^ r`, has affine dimension `r`. -/
lemma finrank_direction_affineSpan_modelFn (hx₀ : x₀ ∈ X) :
    Module.finrank ℝ (affineSpan ℝ
      (((X.image (modelFn P X x₀)).image rationalVectorToReal : Finset _) :
        Set (Fin (modelDim P X x₀) → ℝ))).direction = modelDim P X x₀ := by
  rw [coe_image_rationalVectorToReal_modelFn, finrank_direction_affineSpan_of_span_eq_top ?_
    (span_image_intVectorToReal_latticeCoordinates _), Module.finrank_fin_fun]
  exact ⟨_, ⟨_, sub_coordinateMap_mem_translatedCoords P x₀ hx₀, rfl⟩,
    by simp [latticeCoordinates_zero]⟩

/-- The dimension of the model is at most the Freiman dimension of `X`. -/
lemma modelDim_le_freimanDim (hP : (P + P).Proper) (hXP : X ⊆ P.toFinset) (hx₀ : x₀ ∈ X) :
    modelDim P X x₀ ≤ freimanDim X :=
  le_freimanDim_of_model ((integerGeneratedRank_le_card _).trans card_image_le)
    ⟨modelFn P X x₀, modelFn_isAddFreimanIso hP hXP, finrank_direction_affineSpan_modelFn hx₀⟩

end

end ChangFreimanRuzsa
