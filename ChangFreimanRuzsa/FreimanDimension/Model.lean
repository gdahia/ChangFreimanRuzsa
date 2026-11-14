/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GeometryOfNumbers.LatticeCoordinates
public import SumOfSetsInSeveralDimensions.FreimanDimension

/-!
# A Freiman model in the lattice spanned by a set of integer vectors

Let `f : G → (Fin d → ℤ)` be a Freiman isomorphism of order `2` from a finite set `X` onto its
image, and let `x₀ ∈ X`. Translate the vectors `f x` with `x ∈ X` so that `f x₀` is the origin,
and let `r` be the dimension of the real span of the translated vectors. The map that sends
`x ∈ X` to the coordinates of its translated vector in a basis of the lattice of integer points of
that span is a Freiman isomorphism of order `2` from `X` onto a subset of `ℤ ^ r ⊆ ℚ ^ r` that
contains the origin and spans `ℝ ^ r`. Hence `r` is at most the Freiman dimension `freimanDim X`.

## Main definitions

* `translatedCoords f X x₀`: the translated vectors `f x - f x₀` with `x ∈ X`.
* `modelDim f X x₀`: the dimension `r` of their real span.
* `modelFn f X x₀`: the map `G → ℚ ^ r`.

## Main statements

* `modelFn_isAddFreimanIso`: `modelFn f X x₀` is a Freiman isomorphism of order `2` from `X` onto
  its image.
* `finrank_direction_affineSpan_modelFn`: the image of `X` has affine dimension `r`.
* `modelDim_le_freimanDim`: `modelDim f X x₀ ≤ freimanDim X`.
-/

@[expose] public section

open Finset SumOfSetsInSeveralDimensions

namespace ChangFreimanRuzsa

noncomputable section

variable {G : Type*} {d : ℕ} (f : G → (Fin d → ℤ)) (X : Finset G) (x₀ : G)

/-- The vectors `f x - f x₀` with `x ∈ X`. -/
def translatedCoords : Finset (Fin d → ℤ) :=
  X.image fun x ↦ f x - f x₀

/-- The dimension of the real span of `translatedCoords f X x₀`. -/
abbrev modelDim : ℕ := integerGeneratedRank (translatedCoords f X x₀)

/-- The map `G → ℚ ^ r` that sends `x` to the coordinates of `f x - f x₀` in the basis
`integerGeneratedLatticeBasis (translatedCoords f X x₀)`. -/
def modelFn (x : G) : Fin (modelDim f X x₀) → ℚ :=
  fun i ↦ latticeCoordinates (translatedCoords f X x₀) (f x - f x₀) i

variable {X}

lemma sub_mem_translatedCoords {x : G} (hx : x ∈ X) : f x - f x₀ ∈ translatedCoords f X x₀ :=
  mem_image_of_mem _ hx

lemma sub_mem_saturatedSpan {x : G} (hx : x ∈ X) :
    f x - f x₀ ∈ saturatedSpan (translatedCoords f X x₀) :=
  subset_saturatedSpan _ (sub_mem_translatedCoords f x₀ hx)

variable {f x₀}

lemma coe_translatedCoords :
    (translatedCoords f X x₀ : Set (Fin d → ℤ)) = (fun x ↦ f x - f x₀) '' X :=
  coe_image

private lemma intCast_add_intCast_eq_iff {r : ℕ} {a b c e : Fin r → ℤ} :
    ((fun i ↦ (a i : ℚ)) + fun i ↦ (b i : ℚ)) = ((fun i ↦ (c i : ℚ)) + fun i ↦ (e i : ℚ)) ↔
      a + b = c + e := by
  simp only [funext_iff, Pi.add_apply]
  norm_cast

/-- The model map is a Freiman isomorphism of order `2` from `X` onto its image. -/
lemma modelFn_isAddFreimanIso [AddCommGroup G] (hf : IsAddFreimanIso 2 (X : Set G) (f '' X) f) :
    IsAddFreimanIso 2 (X : Set G)
      ((X.image (modelFn f X x₀) : Finset (Fin (modelDim f X x₀) → ℚ)) :
        Set (Fin (modelDim f X x₀) → ℚ)) (modelFn f X x₀) := by
  rw [coe_image]
  obtain ⟨hbij, hadd⟩ := isAddFreimanIso_two.1 hf
  refine isAddFreimanIso_two.2 ⟨Set.InjOn.bijOn_image ?_, ?_⟩
  · intro a ha b hb hab
    apply hbij.injOn ha hb
    apply sub_left_injective (b := f x₀)
    apply latticeCoordinates_injOn _ (sub_mem_saturatedSpan f x₀ ha) (sub_mem_saturatedSpan f x₀ hb)
    ext i
    exact Int.cast_injective (α := ℚ) (congr_fun hab i)
  · intro a ha b hb c hc e he
    refine intCast_add_intCast_eq_iff.trans ?_
    rw [latticeCoordinates_add_eq_add_iff (sub_mem_saturatedSpan f x₀ ha)
      (sub_mem_saturatedSpan f x₀ hb) (sub_mem_saturatedSpan f x₀ hc)
      (sub_mem_saturatedSpan f x₀ he), sub_add_sub_comm, sub_add_sub_comm, sub_left_inj]
    exact hadd a ha b hb c hc e he

/-- The image of `X` under the model map, viewed in `ℝ ^ r`, is the set of the real casts of the
lattice coordinates of the translated vectors. -/
private lemma coe_image_rationalVectorToReal_modelFn :
    (((X.image (modelFn f X x₀)).image rationalVectorToReal : Finset _) :
        Set (Fin (modelDim f X x₀) → ℝ)) =
      intVectorToReal '' (latticeCoordinates (translatedCoords f X x₀) ''
        (translatedCoords f X x₀ : Set (Fin d → ℤ))) := by
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
      (((X.image (modelFn f X x₀)).image rationalVectorToReal : Finset _) :
        Set (Fin (modelDim f X x₀) → ℝ))).direction = modelDim f X x₀ := by
  rw [coe_image_rationalVectorToReal_modelFn, finrank_direction_affineSpan_of_span_eq_top ?_
    (span_image_intVectorToReal_latticeCoordinates _), Module.finrank_fin_fun]
  exact ⟨_, ⟨_, sub_mem_translatedCoords f x₀ hx₀, rfl⟩, by simp [latticeCoordinates_zero]⟩

/-- The dimension of the model is at most the Freiman dimension of `X`. -/
lemma modelDim_le_freimanDim [DecidableEq G] [AddCommGroup G]
    (hf : IsAddFreimanIso 2 (X : Set G) (f '' X) f) (hx₀ : x₀ ∈ X) :
    modelDim f X x₀ ≤ freimanDim X :=
  le_freimanDim_of_model ((integerGeneratedRank_le_card _).trans card_image_le)
    ⟨modelFn f X x₀, modelFn_isAddFreimanIso hf, finrank_direction_affineSpan_modelFn hx₀⟩

end

end ChangFreimanRuzsa
