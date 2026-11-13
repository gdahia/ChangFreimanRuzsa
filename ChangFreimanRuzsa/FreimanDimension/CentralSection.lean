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

Let `K ⊆ ℝ ^ m` be a full symmetric body and `ψ : (Fin m → ℤ) →+ G` a homomorphism into an abelian
group that is injective on the integer points of `2 • K`. Let `X` be a finite set of points
`o + ψ v` with `v` an integer point of `K`, and let `x₀ ∈ X`. Choose `f x ∈ latticePoints K` with
`x = o + ψ (f x)`. Since `K + K = 2 • K`, the map `f` is a Freiman isomorphism of order `2` from `X`
onto its image. The vectors `f x - f x₀` lie in `2 • K`, and their real span `H` has dimension
`r ≤ freimanDim X` by `modelDim_le_freimanDim`. In coordinates of a basis of the integer points of
`H`, the central section `H ∩ 2 • K` is a full symmetric body `K' ⊆ ℝ ^ r`, every `x ∈ X` is
`x₀ + ψ' v` with `v` an integer point of `K'`, and `vol K' ≤ (2 * (m + 2)) ^ m * vol K`.

## Main statements

* `IsFullSymmetricBody.preimage_realOfLatticeCoordinates`: the section of a full symmetric body by
  the span of some of its integer points, in lattice coordinates, is a full symmetric body.
* `IsFullSymmetricBody.volume_real_preimage_realOfLatticeCoordinates_le`: its volume is at most
  `(m + 2) ^ m * vol K`.
* `exists_isFullSymmetricBody_dim_le_freimanDim`: the passage to a body of dimension at most
  `freimanDim X`.
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

/-- **Passage to the Freiman dimension.** Let `K ⊆ ℝ ^ m` be a full symmetric body and `ψ` a
homomorphism injective on the integer points of `2 • K`. If every point of `X` is `o + ψ v` with `v`
an integer point of `K` and `x₀ ∈ X`, then there are a full symmetric body `K' ⊆ ℝ ^ r` with
`r ≤ freimanDim X` and `vol K' ≤ (2 * (m + 2)) ^ m * vol K`, and a homomorphism `ψ'`, such that
every point of `X` is `x₀ + ψ' v` with `v` an integer point of `K'`. -/
lemma exists_isFullSymmetricBody_dim_le_freimanDim [DecidableEq G] (hK : IsFullSymmetricBody K)
    {ψ : (Fin m → ℤ) →+ G} (hψ : InjOn ψ (latticePoints ((2 : ℝ) • K))) {X : Finset G} {o x₀ : G}
    (hX : ∀ x ∈ X, ∃ v ∈ latticePoints K, x = o + ψ v) (hx₀ : x₀ ∈ X) :
    ∃ (r : ℕ) (K' : Set (Fin r → ℝ)) (ψ' : (Fin r → ℤ) →+ G), r ≤ freimanDim X ∧
      IsFullSymmetricBody K' ∧ (∀ x ∈ X, ∃ v ∈ latticePoints K', x = x₀ + ψ' v) ∧
      volume.real K' ≤ (2 * (m + 2)) ^ m * volume.real K := by
  choose! f hfK hfX using hX
  have hS : (translatedCoords f X x₀ : Set (Fin m → ℤ)) ⊆ latticePoints ((2 : ℝ) • K) := by
    rw [coe_translatedCoords]
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_latticePoints, map_sub, ← sub_self_eq_two_smul hK.convex hK.neg_mem]
    exact sub_mem_sub (hfK x hx) (hfK x₀ hx₀)
  refine ⟨modelDim f X x₀, _, ψ.comp (ofLatticeCoordinates _),
    modelDim_le_freimanDim (isAddFreimanIso_two_of_eq_add hK.convex hψ hfK hfX) hx₀,
    (hK.smul one_le_two).preimage_realOfLatticeCoordinates hS, ?_, ?_⟩
  · intro x hx
    refine ⟨latticeCoordinates _ (f x - f x₀), ?_, ?_⟩
    · rw [mem_latticePoints, mem_preimage,
        realOfLatticeCoordinates_latticeCoordinates (sub_mem_saturatedSpan f x₀ hx)]
      exact hS (sub_mem_translatedCoords f x₀ hx)
    · rw [AddMonoidHom.comp_apply, ofLatticeCoordinates_latticeCoordinates
        (sub_mem_saturatedSpan f x₀ hx), map_sub, add_sub, eq_sub_iff_add_eq]
      conv_lhs => rw [hfX x hx]
      conv_rhs => rw [hfX x₀ hx₀]
      abel
  · grw [(hK.smul one_le_two).volume_real_preimage_realOfLatticeCoordinates_le hS,
      volume_real_smul zero_le_two, mul_pow]
    apply le_of_eq
    ring

end ChangFreimanRuzsa
