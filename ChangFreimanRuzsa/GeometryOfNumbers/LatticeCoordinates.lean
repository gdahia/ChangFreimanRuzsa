/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GAP.Basic
public import ChangFreimanRuzsa.GeometryOfNumbers.IntegerLattice

/-!
# Coordinates in a basis of the lattice of integer points of a span

Let `S` be a finite subset of `ℤ ^ d`, let `H` be its real span and let `r = finrank ℝ H`. By
`finrank_subspaceIntegerLattice_integerGeneratedSubspace`, the integer points of `H` form a lattice
of rank `r`, the subgroup `Λ = saturatedSpan S` of `ℤ ^ d`. This file fixes a basis of that lattice
and defines the map that sends a vector of `r` coordinates to the combination of the basis with
these coefficients, over `ℤ` and over `ℝ`. It also defines the inverse map `ℤ ^ d → ℤ ^ r`, which
sends a point of `Λ` to its coordinates in the basis and is zero outside `Λ`. On `Λ` it is additive.
The coordinates of the points of `S` span `ℝ ^ r`, so in these coordinates `S` is not contained in
a proper subspace.

## Main definitions

* `integerGeneratedRank S`: the dimension `r` of the real span of `S`.
* `integerGeneratedLatticeBasis S`: a basis of the lattice of integer points of `H`, indexed by
  `Fin r`.
* `ofLatticeCoordinates S`: the homomorphism `ℤ ^ r →+ ℤ ^ d` that sends `v` to the integer point
  of `H` with coordinates `v` in the basis.
* `realOfLatticeCoordinates S`: the linear map `ℝ ^ r →ₗ[ℝ] ℝ ^ d` that sends `x` to the point of
  `H` with coordinates `x` in the basis.
* `latticeCoordinates S`: the coordinate map `ℤ ^ d → ℤ ^ r`.

## Main statements

* `realOfLatticeCoordinates_injective`, `range_realOfLatticeCoordinates`: the real map is
  injective and its range is `H`.
* `realOfLatticeCoordinates_intVectorToReal`: the real map extends the integer one.
* `ofLatticeCoordinates_latticeCoordinates`, `latticeCoordinates_ofLatticeCoordinates`: the maps
  `latticeCoordinates S` and `ofLatticeCoordinates S` are inverse bijections between `Λ` and
  `ℤ ^ r`.
* `latticeCoordinates_add`: the coordinate map is additive on `Λ`.
* `span_image_intVectorToReal_latticeCoordinates`: the coordinates of the points of `S` span
  `ℝ ^ r`.
-/

@[expose] public section

open Finset

namespace ChangFreimanRuzsa

noncomputable section

variable {d : ℕ} (S : Finset (Fin d → ℤ))

/-- The dimension of the real span of `S`. It is the rank of the lattice of integer points of the
span. -/
abbrev integerGeneratedRank : ℕ := Module.finrank ℝ (integerGeneratedSubspace S)

lemma integerGeneratedRank_le : integerGeneratedRank S ≤ d := by
  simpa using Submodule.finrank_le (integerGeneratedSubspace S)

lemma integerGeneratedRank_le_card : integerGeneratedRank S ≤ #S := by
  rw [integerGeneratedRank, integerGeneratedSubspace, ← coe_image]
  exact (finrank_span_finset_le_card _).trans card_image_le

/-- A basis of the lattice of integer points of the real span of `S`, indexed by
`Fin (integerGeneratedRank S)`. -/
def integerGeneratedLatticeBasis :
    Module.Basis (Fin (integerGeneratedRank S)) ℤ
      (subspaceIntegerLattice (integerGeneratedSubspace S)) :=
  Module.finBasisOfFinrankEq ℤ _ (finrank_subspaceIntegerLattice_integerGeneratedSubspace S)

/-- An integer vector whose real cast is the `i`-th vector of `integerGeneratedLatticeBasis S`. -/
def latticeBasisIntVector (i : Fin (integerGeneratedRank S)) : Fin d → ℤ :=
  (exists_intVectorToReal_of_mem_standardIntegerLattice
    (mem_standardIntegerLattice_of_mem_subspaceIntegerLattice
      (integerGeneratedLatticeBasis S i).property)).choose

lemma intVectorToReal_latticeBasisIntVector (i : Fin (integerGeneratedRank S)) :
    intVectorToReal (latticeBasisIntVector S i) =
      ((integerGeneratedLatticeBasis S i : integerGeneratedSubspace S) : Fin d → ℝ) :=
  (exists_intVectorToReal_of_mem_standardIntegerLattice
    (mem_standardIntegerLattice_of_mem_subspaceIntegerLattice
      (integerGeneratedLatticeBasis S i).property)).choose_spec

/-- The homomorphism `ℤ ^ r →+ ℤ ^ d` that sends `v` to the integer point of the span of `S` with
coordinates `v` in `integerGeneratedLatticeBasis S`. -/
def ofLatticeCoordinates : (Fin (integerGeneratedRank S) → ℤ) →+ (Fin d → ℤ) :=
  stepsHom (latticeBasisIntVector S)

/-- The linear map `ℝ ^ r →ₗ[ℝ] ℝ ^ d` that sends `x` to the point of the span of `S` with
coordinates `x` in `integerGeneratedLatticeBasis S`. -/
def realOfLatticeCoordinates : (Fin (integerGeneratedRank S) → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
  (integerGeneratedSubspace S).subtype ∘ₗ
    ((integerGeneratedLatticeBasis S).ofZLatticeBasis ℝ _).equivFun.symm.toLinearMap

lemma realOfLatticeCoordinates_injective : Function.Injective (realOfLatticeCoordinates S) :=
  Subtype.val_injective.comp (LinearEquiv.injective _)

lemma range_realOfLatticeCoordinates :
    LinearMap.range (realOfLatticeCoordinates S) = integerGeneratedSubspace S := by
  rw [realOfLatticeCoordinates, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    Submodule.range_subtype]

lemma realOfLatticeCoordinates_mem (x : Fin (integerGeneratedRank S) → ℝ) :
    realOfLatticeCoordinates S x ∈ integerGeneratedSubspace S :=
  range_realOfLatticeCoordinates S ▸ LinearMap.mem_range_self _ x

/-- The map `realOfLatticeCoordinates S` extends `ofLatticeCoordinates S`. -/
lemma realOfLatticeCoordinates_intVectorToReal (v : Fin (integerGeneratedRank S) → ℤ) :
    realOfLatticeCoordinates S (intVectorToReal v) =
      intVectorToReal (ofLatticeCoordinates S v) := by
  rw [ofLatticeCoordinates, stepsHom_apply, map_sum, realOfLatticeCoordinates,
    LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply, map_sum]
  congr with i : 1
  rw [map_zsmul, intVectorToReal_latticeBasisIntVector, map_smul,
    Module.Basis.ofZLatticeBasis_apply, ← Int.cast_smul_eq_zsmul ℝ]
  rfl

lemma ofLatticeCoordinates_mem (v : Fin (integerGeneratedRank S) → ℤ) :
    ofLatticeCoordinates S v ∈ saturatedSpan S := by
  rw [mem_saturatedSpan, ← realOfLatticeCoordinates_intVectorToReal]
  exact realOfLatticeCoordinates_mem S _

open Classical in
/-- The coordinates in `integerGeneratedLatticeBasis S` of an integer point of the real span of
`S`. The value at an integer vector outside the span is zero. -/
def latticeCoordinates (y : Fin d → ℤ) : Fin (integerGeneratedRank S) → ℤ :=
  if hy : y ∈ saturatedSpan S then
    fun i ↦ (integerGeneratedLatticeBasis S).repr
      ⟨⟨intVectorToReal y, hy⟩, intVectorToReal_mem_standardIntegerLattice y⟩ i
  else 0

variable {S}

/-- The point of the span of `S` with the coordinates of `y` is `y`. -/
lemma realOfLatticeCoordinates_latticeCoordinates {y : Fin d → ℤ}
    (hy : y ∈ saturatedSpan S) :
    realOfLatticeCoordinates S (intVectorToReal (latticeCoordinates S y)) = intVectorToReal y := by
  have h : intVectorToReal (latticeCoordinates S y) =
      ((integerGeneratedLatticeBasis S).ofZLatticeBasis ℝ _).equivFun ⟨intVectorToReal y, hy⟩ := by
    ext i
    rw [latticeCoordinates, dite_eq_left hy]
    exact (Module.Basis.ofZLatticeBasis_repr_apply ℝ _ (integerGeneratedLatticeBasis S)
      ⟨⟨intVectorToReal y, hy⟩, intVectorToReal_mem_standardIntegerLattice y⟩ i).symm
  rw [realOfLatticeCoordinates, LinearMap.comp_apply, h, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rfl

lemma ofLatticeCoordinates_latticeCoordinates {y : Fin d → ℤ}
    (hy : y ∈ saturatedSpan S) :
    ofLatticeCoordinates S (latticeCoordinates S y) = y := by
  apply intVectorToReal_injective
  rw [← realOfLatticeCoordinates_intVectorToReal, realOfLatticeCoordinates_latticeCoordinates hy]

variable (S)

lemma latticeCoordinates_ofLatticeCoordinates (v : Fin (integerGeneratedRank S) → ℤ) :
    latticeCoordinates S (ofLatticeCoordinates S v) = v := by
  apply intVectorToReal_injective
  apply realOfLatticeCoordinates_injective S
  rw [realOfLatticeCoordinates_latticeCoordinates (ofLatticeCoordinates_mem S v),
    realOfLatticeCoordinates_intVectorToReal]

lemma ofLatticeCoordinates_injective : Function.Injective (ofLatticeCoordinates S) :=
  Function.LeftInverse.injective (latticeCoordinates_ofLatticeCoordinates S)

lemma latticeCoordinates_injOn : Set.InjOn (latticeCoordinates S) (saturatedSpan S) := by
  intro a ha b hb hab
  rw [← ofLatticeCoordinates_latticeCoordinates ha, hab, ofLatticeCoordinates_latticeCoordinates hb]

lemma latticeCoordinates_zero : latticeCoordinates S 0 = 0 := by
  simpa using latticeCoordinates_ofLatticeCoordinates S 0

variable {S}

lemma latticeCoordinates_add {a b : Fin d → ℤ} (ha : a ∈ saturatedSpan S)
    (hb : b ∈ saturatedSpan S) :
    latticeCoordinates S (a + b) = latticeCoordinates S a + latticeCoordinates S b := by
  apply ofLatticeCoordinates_injective S
  rw [map_add, ofLatticeCoordinates_latticeCoordinates ha,
    ofLatticeCoordinates_latticeCoordinates hb,
    ofLatticeCoordinates_latticeCoordinates (add_mem ha hb)]

/-- On the integer points of the span of `S`, the coordinate map preserves and reflects the
equality of two sums of two terms. -/
lemma latticeCoordinates_add_eq_add_iff {a b c e : Fin d → ℤ}
    (ha : a ∈ saturatedSpan S) (hb : b ∈ saturatedSpan S)
    (hc : c ∈ saturatedSpan S) (he : e ∈ saturatedSpan S) :
    latticeCoordinates S a + latticeCoordinates S b =
      latticeCoordinates S c + latticeCoordinates S e ↔ a + b = c + e := by
  rw [← latticeCoordinates_add ha hb, ← latticeCoordinates_add hc he]
  exact (latticeCoordinates_injOn S).eq_iff (add_mem ha hb) (add_mem hc he)

variable (S)

/-- The real casts of the coordinates of the points of `S` span `ℝ ^ r`. -/
lemma span_image_intVectorToReal_latticeCoordinates :
    Submodule.span ℝ (intVectorToReal '' (latticeCoordinates S '' (S : Set (Fin d → ℤ)))) = ⊤ := by
  apply Submodule.map_injective_of_injective (realOfLatticeCoordinates_injective S)
  rw [Submodule.map_span, Set.image_image, Set.image_image, Submodule.map_top,
    range_realOfLatticeCoordinates, integerGeneratedSubspace]
  congr 1
  apply Set.image_congr
  intro y hy
  exact realOfLatticeCoordinates_latticeCoordinates (subset_saturatedSpan S hy)

end

end ChangFreimanRuzsa
