/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.FreimanModel
public import ChangFreimanRuzsa.Properization.ShortRelationsAndIteration
import ChangFreimanRuzsa.Reboxing.GaugeInduction

/-!
# Reducing the dimension of a progression to the Freiman dimension

Let `q` be a prime, let `P` be a `2`-proper generalized arithmetic progression in `ZMod q` and let
`X ⊆ P` be nonempty. If `P` is small enough compared with `q`, then `X` lies in a `2`-proper
progression of dimension at most `freimanDim X` and of size at most a constant multiple of `|P|`,
where the constant depends only on the dimension of `P`.

The construction is the one of Appendix A of Marcelo Campos, Gabriel Dahia and João Pedro
Marciano, *On the independence number of sparser random Cayley graphs*, J. London Math. Soc. 110
(2024). Fix `x₀ ∈ X` and translate the coefficient vectors in `P` of the elements of `X` so that
the vector of `x₀` is the origin. Let `H` be the real span of the translated vectors and let
`r = dim H`. The differences of two coefficient vectors lie in the symmetric coefficient box of
`P`. Restrict this box to `H` and take coordinates in a basis of the lattice of integer points of
`H`. The result is a symmetric convex body in `ℝ^r` whose integer points span `ℝ^r`, so they are
covered by a proper progression of dimension `r` in `ℤ^r` with at most `boxReboxingFactor r` times
as many points. The image of that progression under the homomorphism `ℤ^r → ZMod q` that sends
coordinates to the corresponding combination of the steps of `P`, translated by `x₀`, contains `X`.
Its dimension `r` is the dimension of the Freiman model of `FreimanModel.lean`, so
`r ≤ freimanDim X`. Finally `exists_twoProperGAP_container` makes the progression `2`-proper
without increasing its dimension.

The same construction works in a torsion-free group, for instance in `ℤ`, with no condition on the
size of `P`. Both cases follow from one statement for a group in which the multiples `n • a` with
`n < N` of every nonzero `a` are distinct.

## Main definitions

* `coordinateReductionConstant`: the constant in the exponent of the size bound.

## Main statements

* `exists_twoProperGAP_dim_le_freimanDim`: the reduction to dimension at most `freimanDim X` in
  `ZMod q`.
* `exists_twoProperGAP_dim_le_freimanDim_of_isAddTorsionFree`: the reduction in a torsion-free
  group.
-/

@[expose] public section

open Finset SumOfSetsInSeveralDimensions
open scoped Topology

namespace ChangFreimanRuzsa

noncomputable section

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-! ## The symmetric coefficient box -/

private lemma card_symBox_le (P : GAP G) : #(symBox P) ≤ 2 ^ P.dim * ∏ i, P.length i := by
  rw [symBox, Pi.card_Icc, ← Fin.prod_const, ← prod_mul_distrib]
  gcongr with i
  rw [Int.card_Icc]
  grind

private lemma sub_coordinateMap_mem_symBox (P : GAP G) (x y : G) :
    P.coordinateMap x - P.coordinateMap y ∈ symBox P := by
  refine mem_symBox.2 fun i ↦ ?_
  have hx := (P.coefficientsFin x i).2
  have hy := (P.coefficientsFin y i).2
  change |(P.coefficientsFin x i : ℤ) - P.coefficientsFin y i| < _
  grind

private lemma mem_symBox_iff_intVectorToReal_mem_realBox {P : GAP G} {v : Fin P.dim → ℤ} :
    v ∈ symBox P ↔ intVectorToReal v ∈ BoxLattice.realBox P.halfWidth := by
  rw [mem_symBox, BoxLattice.mem_realBox]
  refine forall_congr' fun i ↦ ?_
  rw [intVectorToReal, ← Int.cast_abs, ← Int.cast_natCast (R := ℝ), Int.cast_le, GAP.halfWidth]
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
    (hy : y ∈ integerGeneratedLattice S) (hbox : y ∈ symBox P) :
    latticeCoordinates S y ∈ sliceCoords P S := by
  rwa [sliceCoords, mem_preimage, ofLatticeCoordinates_latticeCoordinates hy]

private lemma card_sliceCoords_le (hP : P.Proper) :
    (#(sliceCoords P S) : ℝ) ≤ 2 ^ P.dim * #P.carrier := by
  rw [P.card_eq_prod_length hP]
  exact_mod_cast (card_le_card_of_injOn _ (fun _ hv ↦ mem_preimage.1 hv)
    (ofLatticeCoordinates_injective S).injOn).trans (card_symBox_le P)

private lemma convex_sliceBody : Convex ℝ (sliceBody P S) :=
  (BoxLattice.convex_realBox _).linear_preimage _

private lemma neg_mem_sliceBody (x : Fin (integerGeneratedRank S) → ℝ) (hx : x ∈ sliceBody P S) :
    -x ∈ sliceBody P S := by
  rw [sliceBody, Set.mem_preimage, map_neg]
  exact BoxLattice.neg_mem_realBox _ _ hx

private lemma isCompact_sliceBody : IsCompact (sliceBody P S) := by
  obtain ⟨K, -, hK⟩ := (realOfLatticeCoordinates S).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.2 (realOfLatticeCoordinates_injective S))
  exact Metric.isCompact_of_isClosed_isBounded
    ((BoxLattice.isClosed_realBox _).preimage (LinearMap.continuous_of_finiteDimensional _))
    (hK.isBounded_preimage (BoxLattice.isBounded_realBox _))

variable {P S}

/-- If `S` lies in the symmetric box of `P`, then the span of `S` lies in every coordinate
hyperplane along which `P` has length one. -/
private lemma apply_eq_zero_of_mem_integerGeneratedSubspace (hS : ∀ v ∈ S, v ∈ symBox P)
    {x : Fin P.dim → ℝ} (hx : x ∈ integerGeneratedSubspace S) {i : Fin P.dim}
    (hi : P.length i = 1) : x i = 0 := by
  suffices h : integerGeneratedSubspace S ≤
      LinearMap.ker (LinearMap.proj i : (Fin P.dim → ℝ) →ₗ[ℝ] ℝ) from h hx
  apply Submodule.span_le.2
  rintro _ ⟨v, hv, rfl⟩
  have hvi : v i = 0 := by grind [abs_lt.1 (mem_symBox.1 (hS v hv) i)]
  simp [intVectorToReal, hvi]

private lemma sliceBody_mem_nhds (hS : ∀ v ∈ S, v ∈ symBox P) :
    sliceBody P S ∈ 𝓝 (0 : Fin (integerGeneratedRank S) → ℝ) := by
  have hball : realOfLatticeCoordinates S ⁻¹' Metric.ball 0 1 ∈ 𝓝 0 :=
    (LinearMap.continuous_of_finiteDimensional _).continuousAt.preimage_mem_nhds
      (by simpa using Metric.ball_mem_nhds (0 : Fin P.dim → ℝ) one_pos)
  refine Filter.mem_of_superset hball fun x hx i ↦ ?_
  rw [Set.mem_preimage, mem_ball_zero_iff] at hx
  by_cases hi : P.length i = 1
  · rw [apply_eq_zero_of_mem_integerGeneratedSubspace hS (realOfLatticeCoordinates_mem S x) hi,
      abs_zero]
    exact Nat.cast_nonneg _
  · have hnorm : |realOfLatticeCoordinates S x i| ≤ ‖realOfLatticeCoordinates S x‖ :=
      norm_le_pi_norm (realOfLatticeCoordinates S x) i
    have hwidth : (1 : ℝ) ≤ P.halfWidth i := by
      rw [Nat.one_le_cast, GAP.halfWidth]
      grind [P.length_pos i]
    linarith

private lemma span_sliceBody_inter_eq_top (hS : ∀ v ∈ S, v ∈ symBox P) :
    Submodule.span ℝ (sliceBody P S ∩
      ((⊤ : AddSubgroup (Fin (integerGeneratedRank S) → ℤ)).map BoxLattice.intCastHom :
        Set (Fin (integerGeneratedRank S) → ℝ))) = ⊤ := by
  apply top_unique
  rw [← span_image_intVectorToReal_latticeCoordinates S]
  apply Submodule.span_mono
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  exact ⟨(mem_sliceCoords_iff P S).1 (latticeCoordinates_mem_sliceCoords P S
    (mem_integerGeneratedLattice_of_mem S hy) (hS y hy)), AddSubgroup.mem_map.2 ⟨_, trivial, rfl⟩⟩

/-! ## Covering the integer points of a convex body by a progression -/

/-- Let `K` be a compact convex neighbourhood of the origin in `ℝ^s` that is symmetric and whose
integer points span `ℝ^s`. The integer points of `K` lie in a proper progression of dimension `s`
with at most `boxReboxingFactor s` times as many points. -/
private lemma exists_proper_GAP_of_convex_body {s : ℕ} {K : Set (Fin s → ℝ)} (hconv : Convex ℝ K)
    (hcompact : IsCompact K) (hK₀ : K ∈ 𝓝 0) (hsymm : ∀ x ∈ K, -x ∈ K)
    (hspan : Submodule.span ℝ (K ∩
      ((⊤ : AddSubgroup (Fin s → ℤ)).map BoxLattice.intCastHom : Set (Fin s → ℝ))) = ⊤)
    {D : Finset (Fin s → ℤ)} (hD : ∀ v, v ∈ D ↔ intVectorToReal v ∈ K) :
    ∃ Q : GAP (Fin s → ℤ), Q.Proper ∧ D ⊆ Q.carrier ∧ Q.dim = s ∧
      #Q.carrier ≤ boxReboxingFactor s * #D := by
  have := BoxLattice.discreteTopology_map (⊤ : AddSubgroup (Fin s → ℤ))
  obtain ⟨B⟩ := exists_gaugeControlledLatticeBox_aux s _ K (by simp) hconv hcompact.isClosed hK₀
    hcompact.isBounded hsymm hspan
  obtain ⟨C, hC⟩ := B.exists_adaptedLatticeBox hconv hcompact.isClosed hK₀
    ((NormedSpace.isVonNBounded_iff ℝ).2 hcompact.isBounded)
    (fun x ↦ ⟨hsymm x, fun hx ↦ by simpa using hsymm _ hx⟩) hD (gaugeReboxingDilation s)
  obtain ⟨Q, hQ, hDQ, hdim, hcard⟩ := C.exists_proper_centeredBoxGAP
  rw [← hcard] at hC
  exact ⟨Q, hQ, hDQ, hdim, hC⟩

/-! ## The progression of dimension `modelDim` -/

private lemma exp_cube_mul_two_pow_mul_le (d : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (((d : ℝ) + 2) ^ 3) * (2 ^ d * x) ≤ Real.exp (2 * ((d : ℝ) + 2) ^ 4) * x := by
  have h : ((d : ℝ) + 2) ^ 3 ≤ ((d : ℝ) + 2) ^ 4 :=
    pow_le_pow_right₀ (by linarith [d.cast_nonneg (α := ℝ)]) (by norm_num)
  rw [← mul_assoc, two_mul, Real.exp_add]
  gcongr
  exact (two_pow_le_exp d).trans (Real.exp_le_exp.2 h)

private lemma boxReboxingFactor_mul_card_sliceCoords_le (P : GAP G) (S : Finset (Fin P.dim → ℤ))
    (hP : P.Proper) :
    (boxReboxingFactor (integerGeneratedRank S) * #(sliceCoords P S) : ℝ) ≤
      Real.exp (2 * ((P.dim : ℝ) + 2) ^ 4) * #P.carrier := by
  refine le_trans ?_ (exp_cube_mul_two_pow_mul_le P.dim (Nat.cast_nonneg _))
  gcongr
  · exact boxReboxingFactor_le_exp_cube (integerGeneratedRank_le S)
  · exact card_sliceCoords_le P S hP

/-- A finite subset `X` of a proper progression `P` lies in a progression of dimension
`modelDim P X x₀` and of size at most `exp (2 * (dim P + 2) ^ 4) * |P|`. -/
private lemma exists_GAP_dim_eq_modelDim (hP : P.Proper) {X : Finset G} (hXP : X ⊆ P.carrier)
    {x₀ : G} (hx₀ : x₀ ∈ X) :
    ∃ Q : GAP G, X ⊆ Q.carrier ∧ Q.dim = modelDim P X x₀ ∧
      (#Q.carrier : ℝ) ≤ Real.exp (2 * ((P.dim : ℝ) + 2) ^ 4) * #P.carrier := by
  have hS : ∀ v ∈ translatedCoords P X x₀, v ∈ symBox P := by
    intro v hv
    obtain ⟨x, -, rfl⟩ := mem_image.1 hv
    exact sub_coordinateMap_mem_symBox P x x₀
  obtain ⟨R, -, hR, hdim, hcard⟩ := exists_proper_GAP_of_convex_body
    (convex_sliceBody P _) (isCompact_sliceBody P _) (sliceBody_mem_nhds hS)
    (neg_mem_sliceBody P _) (span_sliceBody_inter_eq_top hS) fun _ ↦ mem_sliceCoords_iff P _
  refine ⟨(R.map ((stepHom P).comp (ofLatticeCoordinates (translatedCoords P X x₀)))).shift x₀,
    fun x hx ↦ ?_, hdim, ?_⟩
  · have hmem := mem_integerGeneratedLattice_of_mem _
      (sub_coordinateMap_mem_translatedCoords (P := P) (x₀ := x₀) hx)
    refine mem_image.2 ⟨x - x₀, mem_image.2 ⟨_, hR (latticeCoordinates_mem_sliceCoords P _ hmem
      (sub_coordinateMap_mem_symBox P x x₀)), ?_⟩, sub_add_cancel x x₀⟩
    rw [AddMonoidHom.comp_apply, ofLatticeCoordinates_latticeCoordinates hmem, map_sub,
      stepHom_coordinateMap P (hXP hx), stepHom_coordinateMap P (hXP hx₀), sub_sub_sub_cancel_right]
  · exact le_trans (mod_cast (card_image_le.trans card_image_le).trans hcard)
      (boxReboxingFactor_mul_card_sliceCoords_le P _ hP)

/-! ## The reduction -/

/-- The constant in the exponent of the size bound of `exists_twoProperGAP_dim_le_freimanDim`. -/
def coordinateReductionConstant : ℝ := properizationConstant + 2

lemma coordinateReductionConstant_pos : 0 < coordinateReductionConstant :=
  add_pos properizationConstant_pos two_pos

private lemma exp_mul_le_exp_add_two_mul {a c d x y : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) (hdc : d ≤ c)
    (hy : 0 ≤ y) (hyx : y ≤ Real.exp (2 * (c + 2) ^ 4) * x) :
    Real.exp (a * (d + 2) ^ 4) * y ≤ Real.exp ((a + 2) * (c + 2) ^ 4) * x := by
  rw [add_mul, Real.exp_add, mul_assoc]
  gcongr

/-- Let `P` be a `2`-proper progression in a group in which the multiples `n • a` with `n < N` of
every nonzero `a` are distinct, where
`exp (coordinateReductionConstant * (dim P + 2) ^ 4) * |P| ≤ N`. A nonempty set `X ⊆ P` is
contained in a `2`-proper progression of dimension at most `freimanDim X` and of size at most
`exp (coordinateReductionConstant * (dim P + 2) ^ 4) * |P|`. -/
theorem exists_twoProperGAP_dim_le_freimanDim_of_injOn_nsmul {N : ℕ} {X : Finset G} {P : GAP G}
    (hG : ∀ a : G, a ≠ 0 → Set.InjOn (fun n : ℕ ↦ n • a) (Set.Iio N)) (hX : X.Nonempty)
    (hP : P.TwoProper) (hXP : X ⊆ P.carrier)
    (hroom : Real.exp (coordinateReductionConstant * ((P.dim : ℝ) + 2) ^ 4) * #P.carrier ≤ N) :
    ∃ Q : GAP G, Q.TwoProper ∧ X ⊆ Q.carrier ∧ (∀ i, 1 < Q.length i) ∧
      Q.dim ≤ freimanDim X ∧ (#Q.carrier : ℝ) ≤
        Real.exp (coordinateReductionConstant * ((P.dim : ℝ) + 2) ^ 4) * #P.carrier := by
  obtain ⟨x₀, hx₀⟩ := hX
  obtain ⟨Q₀, hXQ₀, hdim, hcard⟩ := exists_GAP_dim_eq_modelDim (P.twoProper_proper hP) hXP hx₀
  have h : Real.exp (properizationConstant * ((Q₀.dim : ℝ) + 2) ^ 4) * #Q₀.carrier ≤
      Real.exp (coordinateReductionConstant * ((P.dim : ℝ) + 2) ^ 4) * #P.carrier :=
    exp_mul_le_exp_add_two_mul properizationConstant_pos.le (Nat.cast_nonneg _)
      (Nat.cast_le.2 (hdim.trans_le (integerGeneratedRank_le _))) (Nat.cast_nonneg _) hcard
  obtain ⟨Q, hQ, hQ₀Q, hlen, hQdim, hQcard⟩ :=
    exists_twoProperGAP_container_of_injOn_nsmul Q₀ hG (h.trans hroom)
  exact ⟨Q, hQ, hXQ₀.trans hQ₀Q, hlen,
    hQdim.trans (hdim.trans_le (modelDim_le_freimanDim hP hXP hx₀)), hQcard.trans h⟩

/-- Let `q` be a prime and let `P` be a `2`-proper progression in `ZMod q` with
`exp (coordinateReductionConstant * (dim P + 2) ^ 4) * |P| ≤ q`. A nonempty set `X ⊆ P` is
contained in a `2`-proper progression of dimension at most `freimanDim X` and of size at most
`exp (coordinateReductionConstant * (dim P + 2) ^ 4) * |P|`. -/
theorem exists_twoProperGAP_dim_le_freimanDim {q : ℕ} {X : Finset (ZMod q)} {P : GAP (ZMod q)}
    (hq : q.Prime) (hX : X.Nonempty) (hP : P.TwoProper) (hXP : X ⊆ P.carrier)
    (hroom : Real.exp (coordinateReductionConstant * ((P.dim : ℝ) + 2) ^ 4) * #P.carrier ≤ q) :
    ∃ Q : GAP (ZMod q), Q.TwoProper ∧ X ⊆ Q.carrier ∧ (∀ i, 1 < Q.length i) ∧
      Q.dim ≤ freimanDim X ∧ (#Q.carrier : ℝ) ≤
        Real.exp (coordinateReductionConstant * ((P.dim : ℝ) + 2) ^ 4) * #P.carrier :=
  exists_twoProperGAP_dim_le_freimanDim_of_injOn_nsmul
    (fun _ ha ↦ GAP.injOn_nsmul_of_prime hq ha) hX hP hXP hroom

/-- Let `P` be a `2`-proper progression in a torsion-free group, for instance in `ℤ`. A nonempty
set `X ⊆ P` is contained in a `2`-proper progression of dimension at most `freimanDim X` and of
size at most `exp (coordinateReductionConstant * (dim P + 2) ^ 4) * |P|`. -/
theorem exists_twoProperGAP_dim_le_freimanDim_of_isAddTorsionFree [IsAddTorsionFree G]
    {X : Finset G} {P : GAP G} (hX : X.Nonempty) (hP : P.TwoProper) (hXP : X ⊆ P.carrier) :
    ∃ Q : GAP G, Q.TwoProper ∧ X ⊆ Q.carrier ∧ (∀ i, 1 < Q.length i) ∧
      Q.dim ≤ freimanDim X ∧ (#Q.carrier : ℝ) ≤
        Real.exp (coordinateReductionConstant * ((P.dim : ℝ) + 2) ^ 4) * #P.carrier :=
  exists_twoProperGAP_dim_le_freimanDim_of_injOn_nsmul
    (fun _ ha ↦ GAP.injOn_nsmul_of_isAddTorsionFree _ ha) hX hP hXP (Nat.le_ceil _)

end

end ChangFreimanRuzsa
