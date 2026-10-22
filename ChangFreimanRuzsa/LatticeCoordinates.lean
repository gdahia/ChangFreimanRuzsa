/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GapToolkit
public import ChangFreimanRuzsa.Lattice

/-!
# A basis of the lattice of integer points of a span

Let `S` be a finite subset of `ℤ ^ d`, let `H` be its real span and let `r = finrank ℝ H`. By
`finrank_subspaceIntegerLattice_integerGeneratedSubspace`, the integer points of `H` form a lattice
of rank `r`. This file fixes a basis of that lattice and defines the map that sends a vector of `r`
coordinates to the combination of the basis with these coefficients, over `ℤ` and over `ℝ`.

## Main definitions

* `integerGeneratedRank S`: the dimension `r` of the real span of `S`.
* `integerGeneratedLatticeBasis S`: a basis of the lattice of integer points of `H`, indexed by
  `Fin r`.
* `ofLatticeCoordinates S`: the homomorphism `ℤ ^ r →+ ℤ ^ d` that sends `v` to the integer point
  of `H` with coordinates `v` in the basis.
* `realOfLatticeCoordinates S`: the linear map `ℝ ^ r →ₗ[ℝ] ℝ ^ d` that sends `x` to the point of
  `H` with coordinates `x` in the basis.

## Main statements

* `realOfLatticeCoordinates_injective`, `range_realOfLatticeCoordinates`: the real map is
  injective and its range is `H`.
* `realOfLatticeCoordinates_intVectorToReal`: the real map extends the integer one.
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

end

end ChangFreimanRuzsa
