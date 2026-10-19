/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.Reboxing.EffectiveLattice
public import SumOfSetsInSeveralDimensions.FreimanDimension

/-!
# A Freiman model of a subset of a `2`-proper progression

Let $P$ be a $2$-proper generalized arithmetic progression in an abelian group $G$, let
$X \subseteq P$ be finite and let $x_0 \in X$. Translate the coefficient vectors in $P$ of the
elements of $X$ so that the vector of $x_0$ is the origin, and let $r$ be the dimension of the real
span of the translated vectors. The map that sends $x \in X$ to the coordinates of its translated
vector in a basis of the lattice of integer points of that span is a Freiman isomorphism of order
$2$ from $X$ onto a subset of $\mathbb{Z}^r \subseteq \mathbb{Q}^r$ that contains the origin and
spans $\mathbb{R}^r$. Hence $r$ is at most the Freiman dimension `freimanDim X`.

This is the model of Appendix A of Marcelo Campos, Gabriel Dahia and João Pedro Marciano, *On the
independence number of sparser random Cayley graphs*, J. London Math. Soc. 110 (2024).

## Main definitions

* `translatedCoords P X x₀`: the translated coefficient vectors of the elements of `X`.
* `modelDim P X x₀`: the dimension $r$ of their real span.
* `modelFn P X x₀`: the map $G \to \mathbb{Q}^r$.

## Main statements

* `modelFn_isAddFreimanIso`: `modelFn P X x₀` is a Freiman isomorphism of order $2$ from $X$ onto
  its image.
* `finrank_direction_affineSpan_modelFn`: the image of $X$ has affine dimension $r$.
* `modelDim_le_freimanDim`: `modelDim P X x₀ ≤ freimanDim X`.
-/

@[expose] public section

open Finset SumOfSetsInSeveralDimensions

namespace ChangFreimanRuzsa

noncomputable section

variable {G : Type*} [DecidableEq G] [AddCommGroup G] (P : GAP G) (X : Finset G) (x₀ : G)

/-- The coefficient vectors in $P$ of the elements of $X$, translated by the coefficient vector of
$x_0$. -/
def translatedCoords : Finset (Fin P.dim → ℤ) :=
  X.image fun x ↦ P.coordinateMap x - P.coordinateMap x₀

/-- The dimension of the real span of `translatedCoords P X x₀`. -/
abbrev modelDim : ℕ := integerGeneratedRank (translatedCoords P X x₀)

/-- The map $G \to \mathbb{Q}^r$ that sends $x$ to the coordinates of its translated coefficient
vector in the basis `integerGeneratedLatticeBasis (translatedCoords P X x₀)`. -/
def modelFn (x : G) : Fin (modelDim P X x₀) → ℚ :=
  fun i ↦ latticeCoordinates (translatedCoords P X x₀) (P.coordinateMap x - P.coordinateMap x₀) i

variable {P X x₀}

lemma coe_translatedCoords :
    (translatedCoords P X x₀ : Set (Fin P.dim → ℤ)) =
      (fun x ↦ P.coordinateMap x - P.coordinateMap x₀) '' X :=
  coe_image

lemma sub_coordinateMap_mem_translatedCoords {x : G} (hx : x ∈ X) :
    P.coordinateMap x - P.coordinateMap x₀ ∈ translatedCoords P X x₀ :=
  mem_image_of_mem _ hx

private lemma sub_coordinateMap_mem_integerGeneratedLattice {x : G} (hx : x ∈ X) :
    P.coordinateMap x - P.coordinateMap x₀ ∈ integerGeneratedLattice (translatedCoords P X x₀) :=
  mem_integerGeneratedLattice_of_mem _ (sub_coordinateMap_mem_translatedCoords hx)

private lemma intCast_add_intCast_eq_iff {r : ℕ} {a b c e : Fin r → ℤ} :
    ((fun i ↦ (a i : ℚ)) + fun i ↦ (b i : ℚ)) = ((fun i ↦ (c i : ℚ)) + fun i ↦ (e i : ℚ)) ↔
      a + b = c + e := by
  simp only [funext_iff, Pi.add_apply]
  norm_cast

/-- The model map is a Freiman isomorphism of order $2$ from $X$ onto its image. -/
lemma modelFn_isAddFreimanIso (hP : P.TwoProper) (hXP : X ⊆ P.carrier) :
    IsAddFreimanIso 2 (X : Set G)
      ((X.image (modelFn P X x₀) : Finset (Fin (modelDim P X x₀) → ℚ)) :
        Set (Fin (modelDim P X x₀) → ℚ)) (modelFn P X x₀) := by
  rw [coe_image]
  refine isAddFreimanIso_two.2 ⟨Set.InjOn.bijOn_image ?_, ?_⟩
  · intro a ha b hb hab
    apply P.coordinateMap_injective_on (P.twoProper_proper hP) (hXP ha) (hXP hb)
    apply sub_left_injective (b := P.coordinateMap x₀)
    apply latticeCoordinates_injOn _ (sub_coordinateMap_mem_integerGeneratedLattice ha)
      (sub_coordinateMap_mem_integerGeneratedLattice hb)
    ext i
    exact Int.cast_injective (α := ℚ) (congr_fun hab i)
  · intro a ha b hb c hc e he
    refine intCast_add_intCast_eq_iff.trans ?_
    rw [latticeCoordinates_add_eq_add_iff (sub_coordinateMap_mem_integerGeneratedLattice ha)
      (sub_coordinateMap_mem_integerGeneratedLattice hb)
      (sub_coordinateMap_mem_integerGeneratedLattice hc)
      (sub_coordinateMap_mem_integerGeneratedLattice he), sub_add_sub_comm, sub_add_sub_comm,
      sub_left_inj]
    exact P.coordinateMap_add_eq_iff hP (hXP ha) (hXP hb) (hXP hc) (hXP he)

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

private lemma finrank_direction_affineSpan_of_span_eq_top {r : ℕ} {T : Set (Fin r → ℝ)}
    (h₀ : 0 ∈ T) (hT : Submodule.span ℝ T = ⊤) :
    Module.finrank ℝ (affineSpan ℝ T).direction = r := by
  rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ h₀,
    (by simp : (· -ᵥ (0 : Fin r → ℝ)) '' T = T), hT, finrank_top, Module.finrank_fin_fun]

/-- The image of $X$ under the model map, viewed in $\mathbb{R}^r$, has affine dimension $r$. -/
lemma finrank_direction_affineSpan_modelFn (hx₀ : x₀ ∈ X) :
    Module.finrank ℝ (affineSpan ℝ
      (((X.image (modelFn P X x₀)).image rationalVectorToReal : Finset _) :
        Set (Fin (modelDim P X x₀) → ℝ))).direction = modelDim P X x₀ := by
  rw [coe_image_rationalVectorToReal_modelFn]
  apply finrank_direction_affineSpan_of_span_eq_top _
    (span_image_intVectorToReal_latticeCoordinates _)
  refine ⟨_, ⟨_, sub_coordinateMap_mem_translatedCoords hx₀, rfl⟩, ?_⟩
  rw [sub_self, latticeCoordinates_zero, intVectorToReal_zero]

/-- The dimension of the model is at most the Freiman dimension of $X$. -/
lemma modelDim_le_freimanDim (hP : P.TwoProper) (hXP : X ⊆ P.carrier) (hx₀ : x₀ ∈ X) :
    modelDim P X x₀ ≤ freimanDim X :=
  le_freimanDim_of_model ((integerGeneratedRank_le_card _).trans card_image_le)
    ⟨modelFn P X x₀, modelFn_isAddFreimanIso hP hXP, finrank_direction_affineSpan_modelFn hx₀⟩

end

end ChangFreimanRuzsa
