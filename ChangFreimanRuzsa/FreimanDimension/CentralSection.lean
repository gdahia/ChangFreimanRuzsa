/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GeometryOfNumbers.LatticeCoordinates
public import ChangFreimanRuzsa.GeometryOfNumbers.SymmetricBody
public import SumOfSetsInSeveralDimensions.FreimanDimension
import ChangFreimanRuzsa.FreimanDimension.Model

/-!
# Central sections of a symmetric body and the Freiman dimension

Let `P` be a convex progression in an abelian group with origin `o`, homomorphism
`ψ : (Fin m → ℤ) →+ G` and body a full symmetric body `K ⊆ ℝ ^ m`, and let `ψ` be injective on the
integer points of `2 • K`. Let `X` be a finite set of points of `P`, and let `x₀ ∈ X`. Choose
`f x ∈ latticePoints K` with `x = o + ψ (f x)`. Since `K + K = 2 • K`, the map `f` is a Freiman
isomorphism of order `2` from `X` onto its image. The vectors `f x - f x₀` lie in `2 • K`, and their
real span `H` has dimension `r ≤ freimanDim X` by `modelDim_le_freimanDim`. In coordinates of a
basis of the integer points of `H`, the central section `H ∩ 2 • K` is a full symmetric body
`K' ⊆ ℝ ^ r`, every `x ∈ X` is `x₀ + ψ' v` with `v` an integer point of `K'`, and
`vol K' ≤ (2 * (m + 2)) ^ m * vol K`.

## Main statements

* `IsFullSymmetricBody.preimage_realOfLatticeCoordinates`: the section of a full symmetric body by
  the span of some of its integer points, in lattice coordinates, is a full symmetric body.
* `IsFullSymmetricBody.volume_real_preimage_realOfLatticeCoordinates_le`: its volume is at most
  `(m + 2) ^ m * vol K`.
* `ConvexProgression.exists_superset_dim_le_freimanDim`: the passage to a convex progression of
  dimension at most `freimanDim X`.
-/

public section

namespace ChangFreimanRuzsa

open MeasureTheory Set SumOfSetsInSeveralDimensions
open scoped Pointwise

variable {G : Type*} [AddCommGroup G] {m : ℕ} {K : Set (Fin m → ℝ)} {S : Finset (Fin m → ℤ)}

namespace IsFullSymmetricBody

variable (hK : IsFullSymmetricBody K) (hS : (S : Set (Fin m → ℤ)) ⊆ latticePoints K)
include hK hS

/-- The section of a full symmetric body `K` by the span of a set `S` of its integer points, in
coordinates of a basis of the integer points of the span, is a full symmetric body. -/
lemma preimage_realOfLatticeCoordinates :
    IsFullSymmetricBody (realOfLatticeCoordinates S ⁻¹' K) where
  convex := hK.convex.linear_preimage _
  isCompact := (LinearMap.isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.2 (realOfLatticeCoordinates_injective S))).isCompact_preimage hK.isCompact
  neg_mem x hx := by simpa using hK.neg_mem _ hx
  nonempty := ⟨0, by simpa using hK.zero_mem⟩
  span_latticePoints := by
    refine eq_top_mono (Submodule.span_mono (image_mono ?_))
      (span_image_intVectorToReal_latticeCoordinates S)
    rintro _ ⟨v, hv, rfl⟩
    rw [mem_latticePoints, mem_preimage,
      realOfLatticeCoordinates_latticeCoordinates (subset_saturatedSpan S hv)]
    exact hS hv

/-- The section of a full symmetric body `K ⊆ ℝ ^ m` by the span of a set of its integer points, in
lattice coordinates, has volume at most `(m + 2) ^ m * vol K`. By van der Corput's theorem, its
volume is at most the number of its integer points of `2 • K'`, and these map injectively to the
integer points of `2 • K`. -/
lemma volume_real_preimage_realOfLatticeCoordinates_le :
    volume.real (realOfLatticeCoordinates S ⁻¹' K) ≤ (m + 2) ^ m * volume.real K := by
  have hK' := hK.preimage_realOfLatticeCoordinates hS
  grw [volume_real_le_ncard_latticePoints_two_smul hK'.convex hK'.isCompact hK'.neg_mem,
    ← (by ring : 2 * (1 + (m : ℝ) / 2) = m + 2), ← hK.ncard_latticePoints_smul_le one_le_two]
  refine Nat.cast_le.2 (ncard_le_ncard_of_injOn (ofLatticeCoordinates S) ?_
    (ofLatticeCoordinates_injective S).injOn (hK.smul one_le_two).finite_latticePoints)
  intro v hv
  rw [mem_latticePoints, ← realOfLatticeCoordinates_intVectorToReal]
  exact smul_preimage_set_subset _ _ _ hv

end IsFullSymmetricBody

/-- If `ψ` is injective on the integer points of `2 • K` and `x = o + ψ (f x)` with `f x` an integer
point of `K` for every `x ∈ X`, then `f` is a Freiman isomorphism of order `2` from `X` onto its
image. -/
private lemma isAddFreimanIso_two_of_eq_add (hK : Convex ℝ K) {ψ : (Fin m → ℤ) →+ G}
    (hψ : InjOn ψ (latticePoints ((2 : ℝ) • K))) {X : Finset G} {o : G} {f : G → (Fin m → ℤ)}
    (hfK : ∀ x ∈ X, f x ∈ latticePoints K) (hfX : ∀ x ∈ X, x = o + ψ (f x)) :
    IsAddFreimanIso 2 (X : Set G) (f '' X) f := by
  have hadd (a : G) (ha : a ∈ X) (b : G) (hb : b ∈ X) :
      f a + f b ∈ latticePoints ((2 : ℝ) • K) := by
    rw [mem_latticePoints, map_add, ← one_add_one_eq_two, hK.add_smul zero_le_one zero_le_one,
      one_smul]
    exact add_mem_add (hfK a ha) (hfK b hb)
  have hsum (a : G) (ha : a ∈ X) (b : G) (hb : b ∈ X) : a + b = o + o + ψ (f a + f b) := by
    conv_lhs => rw [hfX a ha, hfX b hb]
    rw [map_add]
    abel
  refine isAddFreimanIso_two.2 ⟨InjOn.bijOn_image ?_, ?_⟩
  · intro a ha b hb hab
    rw [hfX a ha, hfX b hb, hab]
  · intro a ha b hb c hc e he
    rw [hsum a ha b hb, hsum c hc e he, add_right_inj, hψ.eq_iff (hadd a ha b hb) (hadd c hc e he)]

/-- **Passage to the Freiman dimension.** Let `P` be a `2`-proper convex progression of dimension
`m` whose body is a full symmetric body. If a finite nonempty set `X` lies in `P`, then it lies in a
convex progression of dimension at most `freimanDim X` whose body is a full symmetric body of volume
at most `(2 * (m + 2)) ^ m * vol P.body`. -/
lemma _root_.ConvexProgression.exists_superset_dim_le_freimanDim [DecidableEq G]
    {P : ConvexProgression G} (hP : IsFullSymmetricBody (P.body : Set (Fin P.dim → ℝ)))
    (hP₂ : P.Proper 2) {X : Finset G} (hX : X.Nonempty) (hXP : ∀ x ∈ X, x ∈ P) :
    ∃ Q : ConvexProgression G, Q.dim ≤ freimanDim X ∧
      IsFullSymmetricBody (Q.body : Set (Fin Q.dim → ℝ)) ∧ (∀ x ∈ X, x ∈ Q) ∧
        volume.real (Q.body : Set (Fin Q.dim → ℝ)) ≤
          (2 * (P.dim + 2)) ^ P.dim * volume.real (P.body : Set (Fin P.dim → ℝ)) := by
  obtain ⟨x₀, hx₀⟩ := hX
  choose! f hfK hfX using fun x (hx : x ∈ X) ↦
    ConvexProgression.mem_iff_exists_latticePoints.1 (hXP x hx)
  have hS : (translatedCoords f X x₀ : Set (Fin P.dim → ℤ)) ⊆
      latticePoints ((2 : ℝ) • (P.body : Set (Fin P.dim → ℝ))) := by
    rw [coe_translatedCoords]
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_latticePoints, map_sub, ← sub_self_eq_two_smul hP.convex hP.neg_mem]
    exact sub_mem_sub (hfK x hx) (hfK x₀ hx₀)
  have hK := (hP.smul one_le_two).preimage_realOfLatticeCoordinates hS
  refine ⟨⟨modelDim f X x₀, x₀, P.hom.comp (ofLatticeCoordinates _), hK.toConvexBody⟩,
    modelDim_le_freimanDim (isAddFreimanIso_two_of_eq_add hP.convex
      (ConvexProgression.proper_iff_injOn.1 hP₂) hfK fun x hx ↦ (hfX x hx).symm) hx₀, hK, ?_, ?_⟩
  · intro x hx
    refine ConvexProgression.mem_iff_exists_latticePoints.2
      ⟨latticeCoordinates _ (f x - f x₀), ?_, ?_⟩
    · simpa [realOfLatticeCoordinates_latticeCoordinates (sub_mem_saturatedSpan f x₀ hx)] using
        hS (sub_mem_translatedCoords f x₀ hx)
    · dsimp only
      rw [AddMonoidHom.comp_apply, ofLatticeCoordinates_latticeCoordinates
        (sub_mem_saturatedSpan f x₀ hx), map_sub, add_sub, sub_eq_iff_eq_add]
      conv_lhs => rw [← hfX x₀ hx₀]
      conv_rhs => rw [← hfX x hx]
      abel
  · refine ((hP.smul one_le_two).volume_real_preimage_realOfLatticeCoordinates_le hS).trans_eq ?_
    rw [volume_real_smul zero_le_two, mul_pow]
    ring

end ChangFreimanRuzsa
