/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.Properization.Iteration
public import SumOfSetsInSeveralDimensions.FreimanDimension
import ChangFreimanRuzsa.FreimanDimension.Model
import ChangFreimanRuzsa.GeometryOfNumbers.GaugeInduction
import ChangFreimanRuzsa.Properization.ExponentialBounds
import ChangFreimanRuzsa.Properization.ShortRelations

/-!
# Reducing the dimension of a progression to the Freiman dimension

Let `q` be a prime, let `P` be a `2`-proper generalized arithmetic progression in `ZMod q`, let
`X ⊆ P.toFinset` be nonempty and let `2 ≤ t`. Write `d` for the dimension of `P`,
`E d = 4 * (d + 2) ^ 3 * log (d + 2)` for `coordinateReductionExponent d` and `F` for
`E d + tProperExponent t (freimanDim X)`. If `exp F * #P.toFinset ≤ q`, then `X` lies in a
`t`-proper progression of dimension at most `freimanDim X` and of size at most
`exp F * #P.toFinset`.

The construction is the one of Appendix A of Marcelo Campos, Gabriel Dahia and João Pedro
Marciano, *On the independence number of sparser random Cayley graphs*, J. London Math. Soc. 110
(2024). Fix `x₀ ∈ X` and translate the coefficient vectors in `P` of the elements of `X` so that
the vector of `x₀` is the origin. Let `H` be the real span of the translated vectors and let
`r = finrank ℝ H`. The difference of two coefficient vectors lies in the symmetric coefficient box
of `P`. Restrict this box to `H` and take coordinates in a basis of the lattice of integer points
of `H`. The result is a symmetric convex body in `ℝ ^ r` whose integer points span `ℝ ^ r`, so they
are covered by a proper progression of dimension `r` in `ℤ ^ r` with at most
`latticeBoxFactor r ≤ (d + 2) ^ (2 * (d + 1) ^ 2)` times as many points. The image of that
progression under the homomorphism `ℤ ^ r →+ ZMod q` that sends coordinates to the corresponding
combination of the steps of `P`, translated by `x₀`, contains `X`. Its dimension `r` is the
dimension of the Freiman model of `ChangFreimanRuzsa.FreimanDimension.Model`, so `r` is at most
`freimanDim X`. Finally `exists_tProperGAP_toFinset_subset_dim_le_card_le_of_injOn_nsmul` makes
the progression `t`-proper without increasing its dimension.

The same construction works in a torsion-free group, for instance in `ℤ`, with no condition on the
size of `P`. Both cases follow from one statement for an abelian group in which the multiples
`n • a` with `n < N` of every nonzero `a` are distinct.

## Main definitions

* `coordinateReductionExponent`: the exponent `4 * (d + 2) ^ 3 * log (d + 2)` of the size bound.

## Main statements

* `exists_tProperGAP_dim_le_freimanDim_of_injOn_nsmul`: the reduction in an abelian group in
  which the multiples `n • a` with `n < N` of every nonzero `a` are distinct.
* `exists_tProperGAP_dim_le_freimanDim`: the reduction to dimension at most `freimanDim X` in
  `ZMod q`.
* `exists_tProperGAP_dim_le_freimanDim_of_isAddTorsionFree`: the reduction in a torsion-free
  group.
-/

@[expose] public section

open Finset SumOfSetsInSeveralDimensions
open scoped Topology

namespace ChangFreimanRuzsa

noncomputable section

variable {G : Type*} [AddCommGroup G]

/-! ## The symmetric coefficient box -/

private lemma card_symBox_le (P : GAP G) : #(symBox P) ≤ 2 ^ P.dim * ∏ i, P.length i := by
  rw [symBox, Pi.card_Icc, ← Fin.prod_const, ← prod_mul_distrib]
  gcongr with i
  rw [Int.card_Icc]
  grind

private lemma sub_coordinateMap_mem_symBox [DecidableEq G] (P : GAP G) (x y : G) :
    P.coordinateMap x - P.coordinateMap y ∈ symBox P := by
  rw [mem_symBox]
  intro i
  change |(P.coeff x i : ℤ) - P.coeff y i| < _
  grind [(P.coeff x i).isLt, (P.coeff y i).isLt]

private lemma translatedCoords_subset_symBox [DecidableEq G] (P : GAP G) (X : Finset G) (x₀ : G) :
    translatedCoords P X x₀ ⊆ symBox P :=
  image_subset_iff.2 fun x _ ↦ sub_coordinateMap_mem_symBox P x x₀

private lemma mem_symBox_iff_intVectorToReal_mem_realBox {P : GAP G} {v : Fin P.dim → ℤ} :
    v ∈ symBox P ↔ intVectorToReal v ∈ BoxLattice.realBox P.halfWidth := by
  rw [mem_symBox, BoxLattice.mem_realBox]
  apply forall_congr'
  intro i
  rw [intVectorToReal_apply, ← Int.cast_abs, ← Int.cast_natCast (R := ℝ), Int.cast_le,
    GAP.halfWidth]
  grind [P.length_pos i]

/-! ## The slice of the coefficient box by a span -/

variable (P : GAP G) (S : Finset (Fin P.dim → ℤ))

/-- The points of the real span of `S` in the real coefficient box of `P`, in the coordinates of
`realOfLatticeCoordinates S`. -/
private def sliceBody : Set (Fin (integerGeneratedRank S) → ℝ) :=
  realOfLatticeCoordinates S ⁻¹' BoxLattice.realBox P.halfWidth

/-- The coordinates of the integer points of the real span of `S` in the symmetric box of `P`. -/
private def sliceCoords : Finset (Fin (integerGeneratedRank S) → ℤ) :=
  (symBox P).preimage (ofLatticeCoordinates S) (ofLatticeCoordinates_injective S).injOn

private lemma mem_sliceCoords_iff {v : Fin (integerGeneratedRank S) → ℤ} :
    v ∈ sliceCoords P S ↔ intVectorToReal v ∈ sliceBody P S := by
  rw [sliceCoords, mem_preimage, mem_symBox_iff_intVectorToReal_mem_realBox,
    ← realOfLatticeCoordinates_intVectorToReal]
  rfl

private lemma latticeCoordinates_mem_sliceCoords {y : Fin P.dim → ℤ}
    (hy : y ∈ saturatedSpan S) (hyP : y ∈ symBox P) :
    latticeCoordinates S y ∈ sliceCoords P S := by
  rwa [sliceCoords, mem_preimage, ofLatticeCoordinates_latticeCoordinates hy]

private lemma card_sliceCoords_le [DecidableEq G] (hP : P.Proper) :
    (#(sliceCoords P S) : ℝ) ≤ 2 ^ P.dim * #P.toFinset := by
  rw [P.card_eq_prod_length hP]
  exact_mod_cast (card_le_card_of_injOn _ (fun _ hv ↦ mem_preimage.1 hv)
    (ofLatticeCoordinates_injective S).injOn).trans (card_symBox_le P)

private lemma convex_sliceBody : Convex ℝ (sliceBody P S) :=
  (BoxLattice.convex_realBox _).linear_preimage _

private lemma neg_mem_sliceBody {x : Fin (integerGeneratedRank S) → ℝ} (hx : x ∈ sliceBody P S) :
    -x ∈ sliceBody P S := by
  rw [sliceBody, Set.mem_preimage, map_neg]
  exact BoxLattice.neg_mem_realBox hx

private lemma isCompact_sliceBody : IsCompact (sliceBody P S) := by
  obtain ⟨K, -, hK⟩ := (realOfLatticeCoordinates S).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.2 (realOfLatticeCoordinates_injective S))
  exact Metric.isCompact_of_isClosed_isBounded
    ((BoxLattice.isClosed_realBox _).preimage (LinearMap.continuous_of_finiteDimensional _))
    (hK.isBounded_preimage (BoxLattice.isBounded_realBox _))

private lemma sliceBody_mem_nhds : sliceBody P S ∈ 𝓝 (0 : Fin (integerGeneratedRank S) → ℝ) := by
  refine Filter.mem_of_superset ((LinearMap.continuous_of_finiteDimensional
    (realOfLatticeCoordinates S)).continuousAt.preimage_mem_nhds
      (by simpa using Metric.ball_mem_nhds (0 : Fin P.dim → ℝ) one_pos)) ?_
  intro x hx
  rw [Set.mem_preimage, mem_ball_zero_iff] at hx
  rw [sliceBody, Set.mem_preimage, BoxLattice.mem_realBox]
  intro i
  linarith [norm_le_pi_norm (realOfLatticeCoordinates S x) i,
    Real.norm_eq_abs (realOfLatticeCoordinates S x i),
    (Nat.one_le_cast.2 (P.halfWidth_pos i) : (1 : ℝ) ≤ P.halfWidth i)]

variable {P S}

private lemma span_sliceBody_inter_eq_top (hS : S ⊆ symBox P) :
    Submodule.span ℝ (sliceBody P S ∩
      ((⊤ : AddSubgroup (Fin (integerGeneratedRank S) → ℤ)).map intVectorToReal :
        Set (Fin (integerGeneratedRank S) → ℝ))) = ⊤ := by
  apply top_unique
  rw [← span_image_intVectorToReal_latticeCoordinates S]
  apply Submodule.span_mono
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  exact ⟨(mem_sliceCoords_iff P S).1 (latticeCoordinates_mem_sliceCoords P S
    (subset_saturatedSpan S hy) (hS hy)), AddSubgroup.mem_map.2 ⟨_, trivial, rfl⟩⟩

/-! ## The progression of dimension `modelDim` -/

variable [DecidableEq G]

/-- Let `P` be a proper progression of dimension `d` and let `S` lie in the symmetric box of `P`.
The integer points of the slice of the box by the span of `S`, in lattice coordinates, lie in a
progression of dimension at most `integerGeneratedRank S` and of size at most
`exp (2 * (d + 2) ^ 2 * log (d + 2)) * #P.toFinset`. -/
private lemma exists_gap_sliceCoords_subset (hP : P.Proper) (hS : S ⊆ symBox P) :
    ∃ R : GAP (Fin (integerGeneratedRank S) → ℤ), sliceCoords P S ⊆ R.toFinset ∧
      R.dim ≤ integerGeneratedRank S ∧
        #R.toFinset ≤ Real.exp (2 * (P.dim + 2) ^ 2 * Real.log (P.dim + 2)) * #P.toFinset := by
  obtain ⟨R, -, hR, hdim, hcard⟩ := exists_proper_gap_of_convex_body (convex_sliceBody P S)
    (isCompact_sliceBody P S) (sliceBody_mem_nhds P S) (fun _ ↦ neg_mem_sliceBody P S)
    (span_sliceBody_inter_eq_top hS) fun _ ↦ mem_sliceCoords_iff P S
  refine ⟨R, hR, hdim, (Nat.cast_le.2 hcard).trans ?_⟩
  push_cast
  refine (mul_le_mul_of_nonneg_left (card_sliceCoords_le P S hP) (Nat.cast_nonneg _)).trans ?_
  rw [← mul_assoc]
  gcongr
  exact latticeBoxFactor_mul_two_pow_le_exp (integerGeneratedRank_le S)

variable {X : Finset G} {x₀ : G}

/-- If a progression `R` covers the lattice coordinates of the integer points of the slice by the
span of `translatedCoords P X x₀`, then `X` lies in the image of `R` under the map that sends
coordinates to the corresponding combination of the steps of `P`, translated by `x₀`. -/
private lemma subset_toFinset_shift_map_of_sliceCoords_subset (hXP : X ⊆ P.toFinset) (hx₀ : x₀ ∈ X)
    {R : GAP (Fin (modelDim P X x₀) → ℤ)}
    (hR : sliceCoords P (translatedCoords P X x₀) ⊆ R.toFinset) :
    X ⊆ ((R.map ((stepHom P).comp (ofLatticeCoordinates (translatedCoords P X x₀)))).shift
      x₀).toFinset := by
  intro x hx
  have hmem := sub_coordinateMap_mem_saturatedSpan P x₀ hx
  rw [GAP.toFinset_shift, GAP.toFinset_map]
  refine mem_image.2 ⟨x - x₀, mem_image.2 ⟨_, hR (latticeCoordinates_mem_sliceCoords P _ hmem
    (sub_coordinateMap_mem_symBox P x x₀)), ?_⟩, sub_add_cancel x x₀⟩
  rw [AddMonoidHom.comp_apply, ofLatticeCoordinates_latticeCoordinates hmem, map_sub,
    stepHom_coordinateMap P (hXP hx), stepHom_coordinateMap P (hXP hx₀), sub_sub_sub_cancel_right]

/-- A finite subset `X` of a proper progression `P` of dimension `d` lies in a progression of
dimension at most `modelDim P X x₀` and of size at most
`exp (2 * (d + 2) ^ 2 * log (d + 2)) * #P.toFinset`. -/
private lemma exists_gap_dim_le_modelDim (hP : P.Proper) (hXP : X ⊆ P.toFinset) (hx₀ : x₀ ∈ X) :
    ∃ Q : GAP G, X ⊆ Q.toFinset ∧ Q.dim ≤ modelDim P X x₀ ∧
      #Q.toFinset ≤ Real.exp (2 * (P.dim + 2) ^ 2 * Real.log (P.dim + 2)) * #P.toFinset := by
  obtain ⟨R, hR, hdim, hcard⟩ :=
    exists_gap_sliceCoords_subset hP (translatedCoords_subset_symBox P X x₀)
  refine ⟨_, subset_toFinset_shift_map_of_sliceCoords_subset hXP hx₀ hR,
    (GAP.dim_map_le _ R).trans hdim, (Nat.cast_le.2 ?_).trans hcard⟩
  rw [GAP.toFinset_shift]
  exact card_image_le.trans (GAP.card_map_le _ R)

/-! ## The reduction -/

/-- The exponent `4 * (d + 2) ^ 3 * log (d + 2)` in the size bound of
`exists_tProperGAP_dim_le_freimanDim`. -/
def coordinateReductionExponent (d : ℝ) : ℝ := 4 * (d + 2) ^ 3 * Real.log (d + 2)

lemma coordinateReductionExponent_nonneg {d : ℝ} (hd : 0 ≤ d) :
    0 ≤ coordinateReductionExponent d :=
  mul_nonneg (mul_nonneg zero_le_four (pow_nonneg (by linarith) 3)) (log_add_two_pos hd).le

lemma coordinateReductionExponent_mono {d d' : ℝ} (hd : 0 ≤ d) (hdd' : d ≤ d') :
    coordinateReductionExponent d ≤ coordinateReductionExponent d' := by
  rw [coordinateReductionExponent, coordinateReductionExponent, mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (add_two_pow_three_mul_log_le hd hdd') zero_le_four

/-- For `0 ≤ d`, `properizationExponent d + 2 * (d + 2) ^ 2 * log (d + 2)` is at most
`coordinateReductionExponent d`. -/
lemma properizationExponent_add_le_coordinateReductionExponent {d : ℝ} (hd : 0 ≤ d) :
    properizationExponent d + 2 * (d + 2) ^ 2 * Real.log (d + 2) ≤
      coordinateReductionExponent d := by
  rw [properizationExponent, coordinateReductionExponent]
  linarith [two_mul_add_two_sq_mul_log_le hd,
    mul_nonneg (pow_nonneg (by linarith : 0 ≤ d + 2) 3) (log_add_two_pos hd).le]

/-- Let `P` be a `2`-proper progression of dimension `d` in an abelian group in which the
multiples `n • a` with `n < N` of every nonzero `a` are distinct, and let `2 ≤ t`. Write `F` for
`coordinateReductionExponent d + tProperExponent t (freimanDim X)` and suppose that
`exp F * #P.toFinset ≤ N`. A nonempty set `X ⊆ P.toFinset` is contained in a `t`-proper progression
of dimension at most `freimanDim X` and of size at most `exp F * #P.toFinset`. -/
lemma exists_tProperGAP_dim_le_freimanDim_of_injOn_nsmul {N t : ℕ} {X : Finset G} {P : GAP G}
    (ht : 2 ≤ t) (hG : ∀ a : G, a ≠ 0 → Set.InjOn (fun n : ℕ ↦ n • a) (Set.Iio N))
    (hX : X.Nonempty) (hP : (P + P).Proper) (hXP : X ⊆ P.toFinset)
    (hPN : Real.exp (coordinateReductionExponent P.dim + tProperExponent t (freimanDim X)) *
      #P.toFinset ≤ N) :
    ∃ Q : GAP G, (t • Q).Proper ∧ X ⊆ Q.toFinset ∧ Q.dim ≤ freimanDim X ∧
      #Q.toFinset ≤
        Real.exp (coordinateReductionExponent P.dim + tProperExponent t (freimanDim X)) *
          #P.toFinset := by
  obtain ⟨x₀, hx₀⟩ := hX
  obtain ⟨Q₀, hXQ₀, hdim, hcard⟩ := exists_gap_dim_le_modelDim hP.of_add_self hXP hx₀
  have hQ₀F := hdim.trans (modelDim_le_freimanDim hP hXP hx₀)
  have hQ₀P : Real.exp (properizationExponent Q₀.dim + tProperExponent t Q₀.dim) * #Q₀.toFinset ≤
      Real.exp (coordinateReductionExponent P.dim + tProperExponent t (freimanDim X)) *
        #P.toFinset := by
    refine (mul_le_mul (Real.exp_le_exp.2 (add_le_add
      (properizationExponent_mono (Nat.cast_nonneg _)
        (Nat.cast_le.2 (hdim.trans (integerGeneratedRank_le _))))
      (tProperExponent_mono ht (Nat.cast_nonneg _) (Nat.cast_le.2 hQ₀F)))) hcard
      (Nat.cast_nonneg _) (Real.exp_nonneg _)).trans ?_
    rw [← mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (Nat.cast_nonneg _)
    linarith [properizationExponent_add_le_coordinateReductionExponent
      (Nat.cast_nonneg (α := ℝ) P.dim)]
  obtain ⟨Q, hQ, hQ₀Q, hQdim, hQcard⟩ :=
    exists_tProperGAP_toFinset_subset_dim_le_card_le_of_injOn_nsmul Q₀ ht hG (hQ₀P.trans hPN)
  exact ⟨Q, hQ, hXQ₀.trans hQ₀Q, hQdim.trans hQ₀F, hQcard.trans hQ₀P⟩

/-- Let `q` be a prime, let `P` be a `2`-proper progression of dimension `d` in `ZMod q` and let
`2 ≤ t`. Write `F` for `coordinateReductionExponent d + tProperExponent t (freimanDim X)` and
suppose that `exp F * #P.toFinset ≤ q`. A nonempty set `X ⊆ P.toFinset` is contained in a
`t`-proper progression of dimension at most `freimanDim X` and of size at most
`exp F * #P.toFinset`. -/
lemma exists_tProperGAP_dim_le_freimanDim {q t : ℕ} {X : Finset (ZMod q)} {P : GAP (ZMod q)}
    (hq : q.Prime) (ht : 2 ≤ t) (hX : X.Nonempty) (hP : (P + P).Proper) (hXP : X ⊆ P.toFinset)
    (hPq : Real.exp (coordinateReductionExponent P.dim + tProperExponent t (freimanDim X)) *
      #P.toFinset ≤ q) :
    ∃ Q : GAP (ZMod q), (t • Q).Proper ∧ X ⊆ Q.toFinset ∧ Q.dim ≤ freimanDim X ∧
      #Q.toFinset ≤
        Real.exp (coordinateReductionExponent P.dim + tProperExponent t (freimanDim X)) *
          #P.toFinset :=
  exists_tProperGAP_dim_le_freimanDim_of_injOn_nsmul ht
    (fun _ ↦ GAP.injOn_nsmul_of_prime hq) hX hP hXP hPq

/-- Let `P` be a `2`-proper progression of dimension `d` in a torsion-free abelian group, for
instance in `ℤ`, and let `2 ≤ t`. Write `F` for
`coordinateReductionExponent d + tProperExponent t (freimanDim X)`. A nonempty set
`X ⊆ P.toFinset` is contained in a `t`-proper progression of dimension at most `freimanDim X` and of
size at most `exp F * #P.toFinset`. -/
lemma exists_tProperGAP_dim_le_freimanDim_of_isAddTorsionFree [IsAddTorsionFree G] {t : ℕ}
    {X : Finset G} {P : GAP G} (ht : 2 ≤ t) (hX : X.Nonempty) (hP : (P + P).Proper)
    (hXP : X ⊆ P.toFinset) :
    ∃ Q : GAP G, (t • Q).Proper ∧ X ⊆ Q.toFinset ∧ Q.dim ≤ freimanDim X ∧
      #Q.toFinset ≤
        Real.exp (coordinateReductionExponent P.dim + tProperExponent t (freimanDim X)) *
          #P.toFinset :=
  exists_tProperGAP_dim_le_freimanDim_of_injOn_nsmul ht
    (fun _ ↦ GAP.injOn_nsmul_of_isAddTorsionFree _) hX hP hXP (Nat.le_ceil _)

end

end ChangFreimanRuzsa
