/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.LatticeCoordinates

/-!
# Integer coordinates of the integer points of a span

Let $S$ be a finite subset of $\mathbb{Z}^d$, let $H$ be its real span and let $r = \dim H$. The
integer points of $H$ form the subgroup $\Lambda$ = `saturatedSpan S` of $\mathbb{Z}^d$. This file
defines the map $\mathbb{Z}^d \to \mathbb{Z}^r$ that sends a point of $\Lambda$ to its coordinates
in the basis `integerGeneratedLatticeBasis S`, and is zero outside $\Lambda$. On $\Lambda$ it is
additive and it is the inverse of `ofLatticeCoordinates S`. The coordinates of the points of $S$
span $\mathbb{R}^r$, so in these coordinates $S$ is not contained in a proper subspace.

## Main definitions

* `latticeCoordinates S`: the coordinate map $\mathbb{Z}^d \to \mathbb{Z}^r$.

## Main statements

* `ofLatticeCoordinates_latticeCoordinates`, `latticeCoordinates_ofLatticeCoordinates`: the maps
  `latticeCoordinates S` and `ofLatticeCoordinates S` are inverse bijections between $\Lambda$ and
  $\mathbb{Z}^r$.
* `latticeCoordinates_add`: the coordinate map is additive on $\Lambda$.
* `span_image_intVectorToReal_latticeCoordinates`: the coordinates of the points of $S$ span
  $\mathbb{R}^r$.
-/

@[expose] public section

namespace ChangFreimanRuzsa

noncomputable section

variable {d : ℕ} (S : Finset (Fin d → ℤ))

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

/-- The real casts of the coordinates of the points of `S` span $\mathbb{R}^r$. -/
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
