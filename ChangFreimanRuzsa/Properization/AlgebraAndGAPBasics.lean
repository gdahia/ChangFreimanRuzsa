/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.Lattice
public import ChangFreimanRuzsa.Reboxing.GaugeBox
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.TensorProduct.Pi
import ChangFreimanRuzsa.Reboxing.GaugeInduction
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-! # Properization of generalized arithmetic progressions

This file develops the lattice-of-relations description of properness and proves
`exists_twoProperGAP_container` by iterated saturated quotient rank reduction.

The main pieces are:

- `GAP.relations`, the kernel of the step homomorphism, and the characterization
  `GAP.twoProper_iff` of properness by the absence of short relations;
- `GAP.ofData` and `GAP.reshape`, which rebuild a progression from prescribed data;
- `GAP.relationMinimum`, the successive minima of the relation lattice with respect to the
  coefficient box, with `GAP.twoProper_of_three_lt_relationMinimum` reading properness off the
  first minimum;
- `GAP.single_natCast_mem_relations` and `GAP.exists_hasIndependentShort_dim`: in `ZMod q` the
  relation lattice contains `q ℤ ^ dim`, so it has full rank and all `dim` successive minima are
  defined, monotone and positive, not only `λ₁`;
- `GAP.exists_smithNormalForm_shortRelations` and
  `GAP.saturatedSpan_shortRelations_le_relations`: the sublattice spanned by all relations below
  the cutoff is saturated in `ℤ ^ dim`, so the quotient is free and `stepHom` factors through it.

The proof quotients simultaneously by the saturated sublattice spanned by all relations below a
successive-minimum cutoff, reboxes the quotient, and iterates the resulting strict dimension drop.
The cubic cost of each step telescopes into the quartic exponent in the final theorem.

The reboxing step is the proved shortest-direction projection construction under
`Chang.Reboxing`; no external geometric input is used.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open scoped Pointwise Topology

noncomputable section

/-- A surjective real projection of an integral box with positive half-widths is a neighborhood
of the origin. -/
lemma image_realBox_mem_nhds_of_surjective {d s : ℕ} (m : Fin d → ℕ)
    (hm : ∀ i, 0 < m i) (π : (Fin d → ℝ) →ₗ[ℝ] (Fin s → ℝ))
    (hπ : Function.Surjective π) :
    π '' BoxLattice.realBox m ∈ 𝓝 (0 : Fin s → ℝ) := by
  rw [← map_zero π]
  exact (LinearMap.isOpenMap_of_finiteDimensional π hπ).image_mem_nhds
    (BoxLattice.realBox_mem_nhds hm)

/-- The projected standard lattice points of a positive coordinate box span the target of every
surjective integral projection. -/
lemma span_image_realBox_inter_standardLattice_eq_top {d s : ℕ} (m : Fin d → ℕ)
    (hm : ∀ i, 0 < m i)
    (π : (Fin d → ℝ) →ₗ[ℝ] (Fin s → ℝ))
    (πz : (Fin d → ℤ) →+ (Fin s → ℤ))
    (hcast : ∀ v, π (BoxLattice.intCastHom v) = BoxLattice.intCastHom (πz v))
    (hπ : Function.Surjective π) :
    Submodule.span ℝ
      ((π '' BoxLattice.realBox m) ∩
        ((((⊤ : AddSubgroup (Fin s → ℤ)).map
          (BoxLattice.intCastHom : (Fin s → ℤ) →+ (Fin s → ℝ)))) :
            Set (Fin s → ℝ))) = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := hπ y
  rw [← (Pi.basisFun ℝ (Fin d)).sum_repr x, map_sum]
  simp_rw [map_smul]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨⟨(Pi.basisFun ℝ (Fin d)) i, ?_, rfl⟩, ?_⟩
  · rw [BoxLattice.mem_realBox]
    intro j
    by_cases hji : j = i
    · subst j
      have hmi : (1 : ℝ) ≤ m i := by exact_mod_cast hm i
      simpa using hmi
    · simp [Pi.basisFun_apply, hji]
  · refine AddSubgroup.mem_map.mpr
      ⟨πz (Pi.single i 1), Set.mem_univ _, ?_⟩
    rw [← hcast]
    congr 1
    ext j
    simp [Pi.basisFun_apply, Pi.single_apply]

/-- Rebox the integer points of a surjective integral projection of a positive coordinate box.
This is the common projected-box theorem used by one-relation and simultaneous properization. -/
theorem exists_proper_GAP_reboxing_image_realBox {d s : ℕ} (m : Fin d → ℕ)
    (hm : ∀ i, 0 < m i)
    (π : (Fin d → ℝ) →ₗ[ℝ] (Fin s → ℝ))
    (πz : (Fin d → ℤ) →+ (Fin s → ℤ))
    (hcast : ∀ v, π (BoxLattice.intCastHom v) = BoxLattice.intCastHom (πz v))
    (hπ : Function.Surjective π)
    (D : Finset (Fin s → ℤ))
    (hD : ∀ v, v ∈ D ↔ BoxLattice.intCastHom v ∈ π '' BoxLattice.realBox m) :
    ∃ P : GAP (Fin s → ℤ), P.Proper ∧ D ⊆ P.carrier ∧ P.dim = s ∧
      P.carrier.card ≤ boxReboxingFactor s * D.card := by
  let K := π '' BoxLattice.realBox m
  have hcompact : IsCompact K := by
    apply (Metric.isCompact_of_isClosed_isBounded
      (BoxLattice.isClosed_realBox m) (BoxLattice.isBounded_realBox m)).image
    exact LinearMap.continuous_of_finiteDimensional π
  have hsymm : ∀ x, x ∈ K ↔ -x ∈ K := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨-y, BoxLattice.neg_mem_realBox m y hy, map_neg π y⟩
    · rintro ⟨y, hy, hyx⟩
      refine ⟨-y, BoxLattice.neg_mem_realBox m y hy, ?_⟩
      rw [map_neg, hyx, neg_neg]
  let L : AddSubgroup (Fin s → ℝ) :=
    (⊤ : AddSubgroup (Fin s → ℤ)).map
      (BoxLattice.intCastHom : (Fin s → ℤ) →+ (Fin s → ℝ))
  let : DiscreteTopology L := BoxLattice.discreteTopology_map ⊤
  let B := Classical.choice <|
    exists_gaugeControlledLatticeBox_aux s L K (by simp)
      ((BoxLattice.convex_realBox m).linear_image π) hcompact.isClosed
      (image_realBox_mem_nhds_of_surjective m hm π hπ) hcompact.isBounded
      (fun x hx ↦ (hsymm x).mp hx)
      (span_image_realBox_inter_standardLattice_eq_top m hm π πz hcast hπ)
  obtain ⟨C, hCcard⟩ :=
    B.exists_adaptedLatticeBox ((BoxLattice.convex_realBox m).linear_image π)
      hcompact.isClosed (image_realBox_mem_nhds_of_surjective m hm π hπ)
      ((NormedSpace.isVonNBounded_iff ℝ).mpr hcompact.isBounded) hsymm
      (fun v ↦ by change v ∈ D ↔ BoxLattice.intCastHom v ∈ K; exact hD v)
      (gaugeReboxingDilation s)
  obtain ⟨P, hPproper, hDP, hPdim, hPcard⟩ :=
    C.exists_proper_centeredBoxGAP
  refine ⟨P, hPproper, hDP, hPdim, ?_⟩
  rw [hPcard, boxReboxingFactor]
  exact hCcard

section Steps

variable {G : Type*} [AddCommGroup G]

/-! ## Properness and the lattice of relations -/

/-- The element of a GAP with prescribed coefficients, read through the step homomorphism. -/
lemma gapMap_eq_stepsHom {d : ℕ} (origin : G) (step : Fin d → G) (length : Fin d → ℕ)
    (w : (i : Fin d) → Fin (length i)) :
    gapMap origin step length w = origin + stepsHom step fun i ↦ ((w i : ℕ) : ℤ) := by
  rw [stepsHom_natCast]
  rfl

/-- A progression is proper exactly when its steps admit no nonzero relation whose coefficients
are bounded by the lengths. -/
lemma injective_gapMap_iff {d : ℕ} (origin : G) (step : Fin d → G) (length : Fin d → ℕ) :
    Function.Injective (gapMap origin step length) ↔
      ∀ v : Fin d → ℤ, stepsHom step v = 0 → (∀ i, |v i| < (length i : ℤ)) → v = 0 := by
  constructor
  · intro hinj v hv hlt
    have hpos : ∀ i, (v i).toNat < length i := by
      intro i
      have := abs_lt.mp (hlt i)
      omega
    have hneg : ∀ i, (-v i).toNat < length i := by
      intro i
      have := abs_lt.mp (hlt i)
      omega
    have hcoeff := hinj (a₁ := fun i ↦ ⟨(v i).toNat, hpos i⟩)
      (a₂ := fun i ↦ ⟨(-v i).toNat, hneg i⟩) ?_
    · funext i
      have hi := congr_arg (fun w ↦ (w i : ℕ)) hcoeff
      simp only [Pi.zero_apply] at hi ⊢
      omega
    · rw [gapMap_eq_stepsHom, gapMap_eq_stepsHom, add_right_inj, ← sub_eq_zero, ← map_sub, ← hv]
      refine congr_arg (stepsHom step) (funext ?_)
      intro i
      simp only [Pi.sub_apply]
      omega
  · intro hrel w₁ w₂ hw
    have hzero := hrel (fun i ↦ (w₁ i : ℤ) - (w₂ i : ℤ)) ?_ ?_
    · funext i
      apply Fin.ext
      have hi := congr_fun hzero i
      simp only [Pi.zero_apply, sub_eq_zero] at hi
      exact_mod_cast hi
    · rw [gapMap_eq_stepsHom, gapMap_eq_stepsHom, add_right_inj] at hw
      change stepsHom step ((fun i ↦ ((w₁ i : ℕ) : ℤ)) - fun i ↦ ((w₂ i : ℕ) : ℤ)) = 0
      rw [map_sub, sub_eq_zero]
      exact hw
    · intro i
      have := (w₁ i).isLt
      have := (w₂ i).isLt
      rw [abs_lt]
      omega

end Steps

/-! ## Listing the coordinates other than a given one

Dropping a coordinate from a progression needs an enumeration of the remaining ones. `skipCoord j`
is the increasing bijection from `Fin (d - 1)` onto the coordinates other than `j`; it is
`Fin.succAbove` written so that it does not need `d` to be presented as a successor. -/

/-! ## Quotient coordinates along a primitive vector

The general properization step does not eliminate a coordinate of a relation. It quotients the
coefficient lattice by that relation. The lemmas in this section provide the integral coordinates
for a one-relation quotient. A primitive vector is a member of some basis of `ℤ ^ d`; deleting its
basis coordinate then realizes the quotient as `ℤ ^ (d - 1)`.

The basis-extension statement is obtained from Smith normal form: divisibility of every coordinate
forces the divisor to be a unit. -/

/-! ### The real quotient map

The temporary reboxing input is the set of integer points of the image of the real coefficient box.
The following base change of an integral basis supplies the real-linear projection whose restriction
to integer vectors is `basisQuotientMap`. -/

/-- An integral basis of `ℤ ^ d`, extended to a real basis of `ℝ ^ d`. -/
noncomputable def basisToReal {d : ℕ} (b : Module.Basis (Fin d) ℤ (Fin d → ℤ)) :
    Module.Basis (Fin d) ℝ (Fin d → ℝ) :=
  (b.baseChange ℝ).map (TensorProduct.piScalarRight ℤ ℝ ℝ (Fin d))

lemma basisToReal_apply {d : ℕ} (b : Module.Basis (Fin d) ℤ (Fin d → ℤ)) (i : Fin d) :
    basisToReal b i = BoxLattice.intCastHom (b i) := by
  ext k
  simp [basisToReal, BoxLattice.intCastHom_apply, Algebra.smul_def]

lemma basisToReal_repr_intCast {d : ℕ} (b : Module.Basis (Fin d) ℤ (Fin d → ℤ))
    (v : Fin d → ℤ) (i : Fin d) :
    (basisToReal b).repr (BoxLattice.intCastHom v) i = (b.repr v i : ℝ) := by
  have hcast : BoxLattice.intCastHom v =
      TensorProduct.piScalarRight ℤ ℝ ℝ (Fin d) (1 ⊗ₜ[ℤ] v) := by
    ext k
    simp [BoxLattice.intCastHom_apply, Algebra.smul_def]
  rw [hcast, basisToReal, Module.Basis.map_repr]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [Module.Basis.baseChange_repr_tmul]
  simp [Algebra.smul_def]

/-! ### Saturated spans of integer vectors

For the full properization step one quotients by all relation directions below a fixed successive
minimum threshold. Their real span meets `ℤ ^ d` in a saturated submodule. Smith normal form has
only unit diagonal entries on such a submodule, so an adapted ambient basis consists of relation
vectors in the eliminated coordinates and honest free quotient coordinates in the remainder. -/

/-- The saturation in `ℤ ^ d` of the submodule generated by `S`: the integer vectors lying in the
real span of `S`. -/
def saturatedSpan {d : ℕ} (S : Finset (Fin d → ℤ)) : Submodule ℤ (Fin d → ℤ) where
  carrier := {v | BoxLattice.intCastHom v ∈ integerGeneratedSubspace S}
  zero_mem' := by
    change BoxLattice.intCastHom 0 ∈ integerGeneratedSubspace S
    rw [map_zero]
    exact Submodule.zero_mem _
  add_mem' {x y} hx hy := by
    change BoxLattice.intCastHom (x + y) ∈ integerGeneratedSubspace S
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  smul_mem' c x hx := by
    change BoxLattice.intCastHom (c • x) ∈ integerGeneratedSubspace S
    rw [BoxLattice.intCastHom_zsmul]
    exact Submodule.smul_mem _ (c : ℝ) hx

lemma subset_saturatedSpan {d : ℕ} (S : Finset (Fin d → ℤ)) :
    (S : Set (Fin d → ℤ)) ⊆ saturatedSpan S := by
  intro v hv
  change intVectorToReal v ∈ integerGeneratedSubspace S
  exact Submodule.subset_span ⟨v, hv, rfl⟩

/-- The real span of an independent finite family of integer vectors has the expected
dimension. -/
lemma finrank_integerGeneratedSubspace_image {d r : ℕ} (v : Fin r → (Fin d → ℤ))
    (hv : LinearIndependent ℤ v) :
    Module.finrank ℝ (integerGeneratedSubspace (Finset.univ.image v)) = r := by
  have hvR : LinearIndependent ℝ (fun i ↦ intVectorToReal (v i)) := by
    change LinearIndependent ℝ (fun i j ↦ (v i j : ℝ))
    have h := (linearIndependent_algebraMap_comp_iff
      (R := ℤ) (S := ℝ) (ι' := Fin d)).mpr hv
    change LinearIndependent ℝ (fun i j ↦ algebraMap ℤ ℝ (v i j)) at h
    exact h
  change Module.finrank ℝ
    (Submodule.span ℝ (intVectorToReal '' (↑(Finset.univ.image v) : Set (Fin d → ℤ)))) = r
  have hset :
      intVectorToReal '' (↑(Finset.univ.image v) : Set (Fin d → ℤ)) =
        Set.range fun i ↦ intVectorToReal (v i) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [Finset.mem_coe, Finset.mem_image] at hz
      obtain ⟨i, -, rfl⟩ := hz
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨v i, by simp, rfl⟩
  rw [hset, finrank_span_eq_card hvR, Fintype.card_fin]

/-- The saturated span and the integer lattice in its real span are the same free
`ℤ`-module. -/
noncomputable def saturatedSpanEquivSubspaceIntegerLattice {d : ℕ}
    (S : Finset (Fin d → ℤ)) :
    saturatedSpan S ≃ₗ[ℤ]
      subspaceIntegerLattice (integerGeneratedSubspace S) := by
  let f : saturatedSpan S →ₗ[ℤ]
      subspaceIntegerLattice (integerGeneratedSubspace S) := {
    toFun v :=
      ⟨⟨intVectorToReal v, v.2⟩, by
        change intVectorToReal (v : Fin d → ℤ) ∈ standardIntegerLattice d
        exact intVectorToReal_mem_standardIntegerLattice (v : Fin d → ℤ)⟩
    map_add' x y := by
      apply Subtype.ext
      apply Subtype.ext
      exact intVectorToReal_add (x : Fin d → ℤ) (y : Fin d → ℤ)
    map_smul' c x := by
      apply Subtype.ext
      apply Subtype.ext
      exact intVectorToReal_zsmul c (x : Fin d → ℤ) }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply intVectorToReal_injective
    have hxy' := congr_arg Subtype.val hxy
    exact congr_arg Subtype.val hxy'
  · intro x
    obtain ⟨v, hv⟩ := exists_intVectorToReal_of_mem_standardIntegerLattice
      (mem_standardIntegerLattice_of_mem_subspaceIntegerLattice x.2)
    refine ⟨⟨v, ?_⟩, ?_⟩
    · change intVectorToReal v ∈ integerGeneratedSubspace S
      rw [hv]
      exact x.1.2
    · apply Subtype.ext
      apply Subtype.ext
      exact hv

lemma finrank_saturatedSpan {d : ℕ} (S : Finset (Fin d → ℤ)) :
    Module.finrank ℤ (saturatedSpan S) =
      Module.finrank ℝ (integerGeneratedSubspace S) := by
  rw [(saturatedSpanEquivSubspaceIntegerLattice S).finrank_eq,
    integerGeneratedSubspace_lattice_rank]

/-- Reduction modulo an independent family: every integer point in its real span is congruent
modulo the integer span to a point in the sum of half-open fundamental intervals. The coordinate
bound below is the box form used in the finite-field saturation argument. -/
lemma exists_congr_span_isShort {d r : ℕ} {L : Fin d → ℕ} {t : ℝ}
    (v : Fin r → (Fin d → ℤ)) (hshort : ∀ j, IsShort L t (v j))
    {x : Fin d → ℤ} (hx : x ∈ saturatedSpan (Finset.univ.image v)) :
    ∃ y : Fin d → ℤ,
      x - y ∈ Submodule.span ℤ (Set.range v) ∧
        ∀ i, |(y i : ℝ)| ≤ (r : ℝ) * (t * (L i : ℝ)) := by
  have hspan :
      intVectorToReal x ∈
        Submodule.span ℝ (Set.range fun j ↦ intVectorToReal (v j)) := by
    change intVectorToReal x ∈ integerGeneratedSubspace (Finset.univ.image v) at hx
    change intVectorToReal x ∈
      Submodule.span ℝ
        (intVectorToReal '' (↑(Finset.univ.image v) : Set (Fin d → ℤ))) at hx
    have hset :
        intVectorToReal '' (↑(Finset.univ.image v) : Set (Fin d → ℤ)) =
          Set.range fun j ↦ intVectorToReal (v j) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        rw [Finset.mem_coe, Finset.mem_image] at hw
        obtain ⟨j, -, rfl⟩ := hw
        exact Set.mem_range_self j
      · rintro ⟨j, rfl⟩
        exact ⟨v j, by simp, rfl⟩
    rwa [hset] at hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hspan
  set y : Fin d → ℤ := x - ∑ j, round (c j) • v j with hy
  refine ⟨y, ?_, ?_⟩
  · rw [hy, sub_sub_cancel]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    exact Submodule.subset_span (Set.mem_range_self j)
  · intro i
    have hycoord : (y i : ℝ) =
        ∑ j, (c j - (round (c j) : ℝ)) * (v j i : ℝ) := by
      have hci := congr_fun hc i
      change ((y i : ℤ) : ℝ) =
        ∑ j, (c j - (round (c j) : ℝ)) * (v j i : ℝ)
      rw [hy, Pi.sub_apply, Int.cast_sub]
      rw [intVectorToReal, Finset.sum_apply] at hci
      simp only [Pi.smul_apply, smul_eq_mul, intVectorToReal] at hci
      rw [Finset.sum_apply, Int.cast_sum]
      simp_rw [Pi.smul_apply, smul_eq_mul, Int.cast_mul]
      rw [← hci]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [hycoord]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    refine (Finset.sum_le_sum (g := fun _ ↦ t * (L i : ℝ)) ?_).trans ?_
    · intro j _
      rw [abs_mul]
      have hround : |c j - (round (c j) : ℝ)| ≤ 1 := (abs_sub_round (c j)).trans (by norm_num)
      have hv := hshort j i
      exact (mul_le_mul_of_nonneg_right hround (abs_nonneg (v j i : ℝ))).trans (by
        simpa only [one_mul] using hv)
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact le_rfl

/-- The translated form of `exists_congr_span_isShort`: if an integer vector differs from a real
vector `b` by the real span of the short family, it has an integral congruent representative
whose coordinates exceed those of `b` by at most the fundamental-parallelepiped bound. -/
lemma exists_congr_close_isShort {d r : ℕ} {L : Fin d → ℕ} {t : ℝ}
    (v : Fin r → (Fin d → ℤ)) (hshort : ∀ j, IsShort L t (v j))
    (z : Fin d → ℤ) (b : Fin d → ℝ)
    (hspan : intVectorToReal z - b ∈
      Submodule.span ℝ (Set.range fun j ↦ intVectorToReal (v j))) :
    ∃ y : Fin d → ℤ,
      z - y ∈ Submodule.span ℤ (Set.range v) ∧
        ∀ i, |(y i : ℝ)| ≤ |b i| + (r : ℝ) * (t * (L i : ℝ)) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hspan
  set y : Fin d → ℤ := z - ∑ j, round (c j) • v j with hy
  refine ⟨y, ?_, ?_⟩
  · rw [hy, sub_sub_cancel]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    exact Submodule.subset_span (Set.mem_range_self j)
  · intro i
    have hycoord : (y i : ℝ) =
        b i + ∑ j, (c j - (round (c j) : ℝ)) * (v j i : ℝ) := by
      have hci := congr_fun hc i
      change ((y i : ℤ) : ℝ) =
        b i + ∑ j, (c j - (round (c j) : ℝ)) * (v j i : ℝ)
      rw [hy, Pi.sub_apply, Int.cast_sub]
      simp only [Pi.sub_apply, intVectorToReal, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at hci
      rw [Finset.sum_apply, Int.cast_sum]
      simp_rw [Pi.smul_apply, smul_eq_mul, Int.cast_mul]
      have hz : (z i : ℝ) = b i + ∑ j, c j * (v j i : ℝ) := by
        linarith
      rw [hz, add_sub_assoc, ← Finset.sum_sub_distrib]
      congr 1
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [hycoord]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    refine (Finset.sum_le_sum (g := fun _ ↦ t * (L i : ℝ)) ?_).trans ?_
    · intro j _
      rw [abs_mul]
      have hround : |c j - (round (c j) : ℝ)| ≤ 1 :=
        (abs_sub_round (c j)).trans (by norm_num)
      exact (mul_le_mul_of_nonneg_right hround (abs_nonneg (v j i : ℝ))).trans (by
        simpa only [one_mul] using hshort j i)
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact le_rfl

/-- Saturation: if a nonzero integer multiple belongs to `saturatedSpan S`, so does the vector. -/
lemma mem_saturatedSpan_of_zsmul_mem {d : ℕ} {S : Finset (Fin d → ℤ)}
    {v : Fin d → ℤ} {c : ℤ} (hc : c ≠ 0) (hcv : c • v ∈ saturatedSpan S) :
    v ∈ saturatedSpan S := by
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hmem := (integerGeneratedSubspace S).smul_mem (c : ℝ)⁻¹ hcv
  rw [BoxLattice.intCastHom_zsmul, inv_smul_smul₀ hcR] at hmem
  exact hmem

/-- Every Smith coefficient of a saturated submodule is a unit. -/
lemma saturatedSpan_smithCoeff_isUnit {d n : ℕ} {S : Finset (Fin d → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin d) n) (i : Fin n) :
    IsUnit (snf.a i) := by
  have ha : snf.a i ≠ 0 := by
    intro hzero
    have h := snf.snf i
    rw [hzero, zero_smul] at h
    exact (snf.bN.ne_zero i) (Subtype.ext h)
  have hbmem : snf.bM (snf.f i) ∈ saturatedSpan S := by
    apply mem_saturatedSpan_of_zsmul_mem ha
    rw [← snf.snf]
    exact (snf.bN i).2
  let y : saturatedSpan S := ⟨snf.bM (snf.f i), hbmem⟩
  have hbasis : snf.bN i = snf.a i • y := by
    exact Subtype.ext (snf.snf i)
  have hcoord := congr_arg (fun x ↦ snf.bN.repr x i) hbasis
  simp only [map_smul, snf.bN.repr_self, Finsupp.single_eq_same] at hcoord
  have hcoord' : 1 = snf.a i * snf.bN.repr y i := by
    simpa only [Finsupp.smul_apply, smul_eq_mul] using hcoord
  exact isUnit_iff_dvd_one.mpr ⟨snf.bN.repr y i, hcoord'⟩

/-- A canonical enumeration of the ambient Smith-basis indices not occupied by the saturated
summand. -/
noncomputable def smithComplementEquiv {d n : ℕ} (f : Fin n ↪ Fin d) :
    Fin (d - n) ≃ {i : Fin d // i ∉ Set.range f} :=
  Fintype.equivOfCardEq (by
    have hrange : Fintype.card {i : Fin d // i ∈ Set.range f} = n := by
      exact (Fintype.card_congr f.toEquivRange).symm.trans (Fintype.card_fin n)
    rw [Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_fin, hrange])

/-- Quotient coordinates associated with the free complement of a Smith-normal-form basis. -/
noncomputable def smithQuotientMap {d n : ℕ} {S : Finset (Fin d → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin d) n) :
    (Fin d → ℤ) →+ (Fin (d - n) → ℤ) where
  toFun x k := snf.bM.repr x (smithComplementEquiv snf.f k)
  map_zero' := by
    ext k
    simp
  map_add' x y := by
    ext k
    simp

/-- The lift with zero coordinates along the saturated Smith summand. -/
noncomputable def smithQuotientLift {d n : ℕ} {S : Finset (Fin d → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin d) n)
    (y : Fin (d - n) → ℤ) : Fin d → ℤ :=
  ∑ k, y k • snf.bM (smithComplementEquiv snf.f k)

lemma smithQuotientMap_lift {d n : ℕ} {S : Finset (Fin d → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin d) n)
    (y : Fin (d - n) → ℤ) :
    smithQuotientMap snf (smithQuotientLift snf y) = y := by
  ext i
  have hinj := (smithComplementEquiv snf.f).injective
  change snf.bM.repr
    (∑ k, y k • snf.bM (smithComplementEquiv snf.f k))
      (smithComplementEquiv snf.f i) = y i
  rw [map_sum]
  simp_rw [map_smul, snf.bM.repr_self]
  change Finsupp.applyAddHom (↑(smithComplementEquiv snf.f i) : Fin d)
    (∑ k, y k • Finsupp.single (↑(smithComplementEquiv snf.f k) : Fin d) (1 : ℤ)) = y i
  rw [map_sum]
  simp_rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  refine (Finset.sum_eq_single (s := Finset.univ)
    (f := fun k : Fin (d - n) ↦
      Finsupp.applyAddHom (↑(smithComplementEquiv snf.f i) : Fin d)
        (Finsupp.single (↑(smithComplementEquiv snf.f k) : Fin d) (y k))) i
    ?_ (fun h ↦ absurd (Finset.mem_univ i) h)).trans ?_
  · intro k _ hki
    rw [Finsupp.applyAddHom_apply, Finsupp.single_apply,
      ite_eq_right fun h ↦ hki (hinj (Subtype.ext h))]
  · rw [Finsupp.applyAddHom_apply, Finsupp.single_eq_same]

lemma smithQuotientMap_eq_zero_iff {d n : ℕ} {S : Finset (Fin d → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin d) n)
    (x : Fin d → ℤ) :
    smithQuotientMap snf x = 0 ↔ x ∈ saturatedSpan S := by
  constructor
  · intro hzero
    rw [← snf.bM.sum_repr x]
    apply Submodule.sum_mem _
    intro k _
    rcases em (k ∈ Set.range snf.f) with ⟨i, rfl⟩ | hk
    · refine Submodule.smul_mem _ _ (mem_saturatedSpan_of_zsmul_mem
        (show snf.a i ≠ 0 by
          exact fun h ↦ (saturatedSpan_smithCoeff_isUnit snf i).ne_zero h) ?_)
      rw [← snf.snf]
      exact (snf.bN i).2
    · have hcoeff : snf.bM.repr x k = 0 := by
        obtain ⟨c, hc⟩ := (smithComplementEquiv snf.f).surjective ⟨k, hk⟩
        have hcval := congr_arg Subtype.val hc
        have hc0 := congr_fun hzero c
        change snf.bM.repr x (smithComplementEquiv snf.f c) = 0 at hc0
        rwa [hcval] at hc0
      rw [hcoeff, zero_smul]
      exact Submodule.zero_mem _
  · intro hx
    ext k
    change snf.bM.repr x (smithComplementEquiv snf.f k) = 0
    exact snf.repr_eq_zero_of_notMem_range ⟨x, hx⟩ (smithComplementEquiv snf.f k).2

lemma smithQuotientMap_eq_iff {d n : ℕ} {S : Finset (Fin d → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin d) n)
    (x y : Fin d → ℤ) :
    smithQuotientMap snf x = smithQuotientMap snf y ↔ x - y ∈ saturatedSpan S := by
  rw [← sub_eq_zero, ← map_sub, smithQuotientMap_eq_zero_iff]

/-! ### The real map for a saturated quotient -/

/-- The real-linear quotient map associated with the free complement in Smith normal form. -/
noncomputable def smithRealQuotientMap {d n : ℕ} {S : Finset (Fin d → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin d) n) :
    (Fin d → ℝ) →ₗ[ℝ] (Fin (d - n) → ℝ) :=
  LinearMap.pi fun k ↦ (basisToReal snf.bM).coord (smithComplementEquiv snf.f k)

/-- On integer vectors, the real Smith quotient is the cast of `smithQuotientMap`. -/
lemma smithRealQuotientMap_intCast {d n : ℕ} {S : Finset (Fin d → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin d) n)
    (v : Fin d → ℤ) :
    smithRealQuotientMap snf (BoxLattice.intCastHom v) =
      BoxLattice.intCastHom (smithQuotientMap snf v) := by
  ext k
  rw [smithRealQuotientMap, LinearMap.pi_apply]
  change (basisToReal snf.bM).repr (BoxLattice.intCastHom v)
      (smithComplementEquiv snf.f k) =
    BoxLattice.intCastHom (smithQuotientMap snf v) k
  rw [basisToReal_repr_intCast]
  rfl

lemma smithRealQuotientMap_surjective {d n : ℕ} {S : Finset (Fin d → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin d) n) :
    Function.Surjective (smithRealQuotientMap snf) := by
  intro y
  use ∑ k, y k • basisToReal snf.bM (smithComplementEquiv snf.f k)
  ext i
  rw [smithRealQuotientMap, LinearMap.pi_apply, map_sum]
  simp only [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
    smul_eq_mul, Finsupp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki
    rw [ite_eq_right fun h ↦ hki ((smithComplementEquiv snf.f).injective (Subtype.ext h)),
      mul_zero]
  · simp

/-- The kernel of the real Smith quotient is exactly the real span being divided out. -/
lemma smithRealQuotientMap_eq_zero_iff {d n : ℕ} {S : Finset (Fin d → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin d) n)
    (x : Fin d → ℝ) :
    smithRealQuotientMap snf x = 0 ↔ x ∈ integerGeneratedSubspace S := by
  constructor
  · intro hzero
    rw [← (basisToReal snf.bM).sum_repr x]
    apply Submodule.sum_mem _
    intro k _
    rcases em (k ∈ Set.range snf.f) with ⟨i, rfl⟩ | hk
    · refine Submodule.smul_mem _ _ ?_
      rw [basisToReal_apply]
      change BoxLattice.intCastHom (snf.bM (snf.f i)) ∈ integerGeneratedSubspace S
      apply mem_saturatedSpan_of_zsmul_mem
        (saturatedSpan_smithCoeff_isUnit snf i).ne_zero
      rw [← snf.snf]
      exact (snf.bN i).2
    · have hcoeff : (basisToReal snf.bM).repr x k = 0 := by
        obtain ⟨c, hc⟩ := (smithComplementEquiv snf.f).surjective ⟨k, hk⟩
        have hcval := congr_arg Subtype.val hc
        have hc0 := congr_fun hzero c
        change (basisToReal snf.bM).repr x (smithComplementEquiv snf.f c) = 0 at hc0
        rwa [hcval] at hc0
      rw [hcoeff, zero_smul]
      exact Submodule.zero_mem _
  · intro hx
    have hle : integerGeneratedSubspace S ≤ LinearMap.ker (smithRealQuotientMap snf) := by
      rw [integerGeneratedSubspace]
      apply Submodule.span_le.mpr
      rintro z ⟨v, hv, rfl⟩
      change smithRealQuotientMap snf (BoxLattice.intCastHom v) = 0
      rw [smithRealQuotientMap_intCast]
      have hvSat : v ∈ saturatedSpan S := subset_saturatedSpan S hv
      rw [(smithQuotientMap_eq_zero_iff snf v).mpr hvSat, map_zero]
    exact LinearMap.mem_ker.mp (hle hx)

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

namespace GAP

/-- The lattice of relations among the steps of a GAP. -/
def relations (P : GAP G) : AddSubgroup (Fin P.dim → ℤ) := (stepHom P).ker

lemma mem_relations {P : GAP G} {v : Fin P.dim → ℤ} :
    v ∈ P.relations ↔ ∑ i, v i • P.step i = 0 := Iff.rfl

/-- The steps on the free complement of a saturated Smith summand. -/
noncomputable def smithQuotientStep (P : GAP G) {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    Fin (P.dim - n) → G :=
  fun k ↦ stepHom P (snf.bM (smithComplementEquiv snf.f k))

/-- If the saturated summand consists of relations, the step homomorphism factors through its
Smith quotient coordinates. -/
lemma stepHom_smithQuotientMap (P : GAP G) {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n)
    (hrel : (saturatedSpan S).toAddSubgroup ≤ P.relations)
    (x : Fin P.dim → ℤ) :
    stepsHom (P.smithQuotientStep snf) (smithQuotientMap snf x) = stepHom P x := by
  have hcoord : smithQuotientMap snf
      (smithQuotientLift snf (smithQuotientMap snf x)) = smithQuotientMap snf x :=
    smithQuotientMap_lift snf _
  have hdiff : smithQuotientLift snf (smithQuotientMap snf x) - x ∈ saturatedSpan S :=
    (smithQuotientMap_eq_iff snf _ _).mp hcoord
  have hlift : stepHom P (smithQuotientLift snf (smithQuotientMap snf x)) = stepHom P x := by
    have hmap : stepHom P
        (smithQuotientLift snf (smithQuotientMap snf x) - x) = 0 := hrel hdiff
    rw [map_sub, sub_eq_zero] at hmap
    exact hmap
  refine Eq.trans ?_ hlift
  rw [stepsHom_apply]
  unfold smithQuotientLift
  rw [map_sum]
  simp_rw [smithQuotientStep, map_zsmul]

lemma twoProper_iff (P : GAP G) :
    P.TwoProper ↔ ∀ v ∈ P.relations, (∀ i, |v i| < 2 * (P.length i : ℤ)) → v = 0 := by
  rw [TwoProper, injective_gapMap_iff]
  apply forall_congr'
  intro v
  refine imp_congr Iff.rfl (imp_congr ?_ Iff.rfl)
  apply forall_congr'
  intro i
  rw [Nat.cast_mul, Nat.cast_ofNat]

/-! ## Replacing the steps and lengths of a progression -/

/-- The GAP with prescribed dimension, origin, steps and lengths. -/
def ofData (d : ℕ) (origin : G) (step : Fin d → G) (length : Fin d → ℕ)
    (hlength : ∀ i, 0 < length i) : GAP G where
  dim := d
  carrier := Finset.univ.image (gapMap origin step length)
  origin := origin
  step := step
  length := length
  length_pos := hlength
  carrier_eq := rfl

lemma mem_ofData (d : ℕ) (origin : G) (step : Fin d → G) (length : Fin d → ℕ)
    (hlength : ∀ i, 0 < length i) (k : (i : Fin d) → Fin (length i)) :
    gapMap origin step length k ∈ (ofData d origin step length hlength).carrier :=
  Finset.mem_image_of_mem _ (Finset.mem_univ k)

/-- Replace the steps and lengths of a GAP, keeping its dimension and origin. -/
def reshape (P : GAP G) (step : Fin P.dim → G) (length : Fin P.dim → ℕ)
    (hlength : ∀ i, 0 < length i) : GAP G :=
  ofData P.dim P.origin step length hlength

/-- Multiply every length of a progression by the same positive integer. -/
def scaleLengths (P : GAP G) (k : ℕ) (hk : 0 < k) : GAP G :=
  P.reshape P.step (fun i ↦ k * P.length i) fun i ↦
    Nat.mul_pos hk (P.length_pos i)

@[simp] lemma scaleLengths_length (P : GAP G) (k : ℕ) (hk : 0 < k) :
    (P.scaleLengths k hk).length = fun i ↦ k * P.length i := rfl

/-- Scaling all coefficient intervals by `k` covers the resulting progression by `k ^ dim`
translates of the original one. -/
theorem card_scaleLengths_le (P : GAP G) (k : ℕ) (hk : 0 < k) :
    (P.scaleLengths k hk).carrier.card ≤ k ^ P.dim * P.carrier.card := by
  let Q := P.scaleLengths k hk
  let block (x : Q.carrier) (i : Fin P.dim) : Fin k :=
    ⟨(Q.coefficientsFin x i : ℕ) / P.length i, by
      have hcoeff := (Q.coefficientsFin x i).isLt
      simp only [Q, scaleLengths_length] at hcoeff
      exact (Nat.div_lt_iff_lt_mul (P.length_pos i)).mpr (by
        simpa only [mul_comm] using hcoeff)⟩
  let residue (x : Q.carrier) (i : Fin P.dim) : Fin (P.length i) :=
    ⟨(Q.coefficientsFin x i : ℕ) % P.length i, Nat.mod_lt _ (P.length_pos i)⟩
  let oldPoint (x : Q.carrier) : P.carrier :=
    ⟨gapMap P.origin P.step P.length (residue x), by
      rw [P.carrier_eq]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  let encode (x : Q.carrier) : (Fin P.dim → Fin k) × P.carrier :=
    ⟨block x, oldPoint x⟩
  have hencode : Function.Injective encode := by
    intro x y hxy
    have hblock : block x = block y := congr_arg Prod.fst hxy
    have hold : (oldPoint x : G) = oldPoint y := congr_arg (fun z ↦ (z.2 : G)) hxy
    apply Subtype.ext
    rw [← Q.coefficientsFin_spec x.2, ← Q.coefficientsFin_spec y.2]
    rw [gapMap, gapMap]
    apply congr_arg (Q.origin + ·)
    change ∑ i, (Q.coefficientsFin x i : ℕ) • P.step i =
      ∑ i, (Q.coefficientsFin y i : ℕ) • P.step i
    have hdecomp : ∀ z : Q.carrier,
        ∑ i, (Q.coefficientsFin z i : ℕ) • P.step i =
          ∑ i, ((block z i : ℕ) * P.length i) • P.step i +
            ∑ i, (residue z i : ℕ) • P.step i := by
      intro z
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← add_nsmul]
      apply congr_arg (· • P.step i)
      rw [mul_comm]
      exact (Nat.div_add_mod (Q.coefficientsFin z i) (P.length i)).symm
    have holdstep : ∀ z : Q.carrier,
        ∑ i, (residue z i : ℕ) • P.step i = (oldPoint z : G) - P.origin := by
      intro z
      change ∑ i, (residue z i : ℕ) • P.step i =
        (P.origin + ∑ i, (residue z i : ℕ) • P.step i) - P.origin
      abel
    rw [hdecomp x, hdecomp y, hblock]
    rw [holdstep x, holdstep y]
    rw [hold]
  have hcard := Fintype.card_le_of_injective encode hencode
  simpa only [Fintype.card_prod, Fintype.card_pi, Fintype.card_fin, Fintype.card_coe,
    Finset.prod_const, Finset.card_univ, Q, Nat.card_eq_fintype_card] using hcard

/-- The step-homomorphism image of the box dilated by `m`. -/
def boundedStepImage (P : GAP G) (m : ℕ) : Finset G :=
  (intBox fun i ↦ m * (P.length i - 1)).image (stepHom P)

/-- A dilated symmetric coefficient box has at most `(2m+1)^dim` translates of the original
progression in its image. -/
theorem card_boundedStepImage_le (P : GAP G) (m : ℕ) :
    (P.boundedStepImage m).card ≤ (2 * m + 1) ^ P.dim * P.carrier.card := by
  set k := 2 * m + 1 with hkdef
  have hk : 0 < k := by omega
  let Q := P.scaleLengths k hk
  let shift : Fin P.dim → ℤ := fun i ↦ (m * (P.length i - 1) : ℕ)
  let f : G → G := fun z ↦ P.origin + stepHom P shift + z
  have hmaps : ∀ z ∈ P.boundedStepImage m, f z ∈ Q.carrier := by
    intro z hz
    rw [boundedStepImage, Finset.mem_image] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    rw [mem_intBox] at hv
    have hcoeff : ∀ i, 0 ≤ v i + shift i ∧
        v i + shift i < (Q.length i : ℤ) := by
      intro i
      have hi := abs_le.mp (hv i)
      have hlen := P.length_pos i
      simp only [shift]
      simp only [Q, scaleLengths_length, hkdef]
      have hcast : (((P.length i - 1 : ℕ) : ℕ) : ℤ) = (P.length i : ℤ) - 1 := by
        omega
      have hmcast : ((m * (P.length i - 1) : ℕ) : ℤ) =
          (m : ℤ) * ((P.length i : ℤ) - 1) := by
        rw [Nat.cast_mul, hcast]
      rw [hmcast] at hi ⊢
      push_cast
      constructor
      · omega
      · nlinarith
    rw [Q.carrier_eq]
    refine Finset.mem_image.mpr
      ⟨fun i ↦ ⟨(v i + shift i).toNat, by
        have := hcoeff i
        omega⟩, Finset.mem_univ _, ?_⟩
    change P.origin + ∑ i : Fin P.dim, (v i + shift i).toNat • P.step i =
      P.origin + stepHom P shift + stepHom P v
    have hcast : (fun i ↦ (((v i + shift i).toNat : ℕ) : ℤ)) = v + shift := by
      funext i
      have := hcoeff i
      simp only [Pi.add_apply]
      rw [Int.toNat_of_nonneg this.1]
    rw [← stepsHom_natCast, hcast, map_add]
    unfold stepHom
    abel
  have hinj : Function.Injective f := by
    intro x y hxy
    change P.origin + stepHom P shift + x = P.origin + stepHom P shift + y at hxy
    exact add_left_cancel hxy
  apply (Finset.card_le_card_of_injOn f hmaps hinj.injOn).trans
  rw [hkdef]
  exact P.card_scaleLengths_le k hk

/-- Enlarging the lengths of a progression enlarges its carrier. -/
lemma carrier_subset_reshape (P : GAP G) (length : Fin P.dim → ℕ) (hlength : ∀ i, 0 < length i)
    (hle : ∀ i, P.length i ≤ length i) :
    P.carrier ⊆ (P.reshape P.step length hlength).carrier := by
  intro x hx
  rw [P.carrier_eq, Finset.mem_image] at hx
  obtain ⟨w, -, rfl⟩ := hx
  exact Finset.mem_image.mpr
    ⟨fun i ↦ ⟨w i, (w i).isLt.trans_le (hle i)⟩, Finset.mem_univ _, rfl⟩

/-! ## Membership through integer coefficients -/

/-- Membership in a progression, in terms of integer coefficients in the coefficient box. -/
lemma mem_carrier_iff_exists_intCoeffs (P : GAP G) {x : G} :
    x ∈ P.carrier ↔ ∃ c : Fin P.dim → ℤ, (∀ i, 0 ≤ c i ∧ c i < (P.length i : ℤ)) ∧
      x = P.origin + stepsHom P.step c := by
  rw [P.carrier_eq, Finset.mem_image]
  constructor
  · rintro ⟨w, -, rfl⟩
    refine ⟨fun i ↦ ((w i : ℕ) : ℤ), ?_, gapMap_eq_stepsHom _ _ _ _⟩
    intro i
    constructor
    · exact Int.natCast_nonneg _
    · change ((w i : ℕ) : ℤ) < (P.length i : ℤ)
      exact_mod_cast (w i).isLt
  · rintro ⟨c, hc, rfl⟩
    refine ⟨?_, Finset.mem_univ _, ?_⟩
    · intro i
      refine ⟨(c i).toNat, ?_⟩
      have := hc i
      omega
    · rw [gapMap_eq_stepsHom]
      refine congr_arg (P.origin + ·) (congr_arg (stepsHom P.step) (funext ?_))
      intro i
      exact Int.toNat_of_nonneg (hc i).1

end GAP

/-- An elementary comparison used to state properization costs uniformly. -/
lemma two_pow_le_exp (d : ℕ) : (2 : ℝ) ^ d ≤ Real.exp (((d : ℝ) + 2) ^ 3) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  apply (pow_le_pow_left₀ (by norm_num) h2 d).trans
  rw [← Real.exp_nat_mul, mul_one]
  apply Real.exp_le_exp.mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) d, sq_nonneg ((d : ℝ) + 2),
    pow_nonneg (Nat.cast_nonneg (α := ℝ) d) 3]

/-- A polynomial base raised to the dimension is absorbed by a cubic exponential. -/
lemma poly_pow_le_exp_cube {d : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (hbound : b ≤ 12 * ((d : ℝ) + 2) ^ 2) :
    b ^ d ≤ Real.exp (12 * ((d : ℝ) + 2) ^ 3) := by
  have hX : 0 ≤ 12 * ((d : ℝ) + 2) ^ 2 := by positivity
  have hbexp : b ≤ Real.exp (12 * ((d : ℝ) + 2) ^ 2) := by
    apply hbound.trans
    linarith [Real.add_one_le_exp (12 * ((d : ℝ) + 2) ^ 2)]
  apply (pow_le_pow_left₀ hb hbexp d).trans
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hd : (d : ℝ) ≤ (d : ℝ) + 2 := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hd hX]

/-- The explicit factor produced by the shortest-direction reboxing induction is absorbed by a
cubic exponential. -/
lemma boxReboxingFactor_le_exp_cube {k d : ℕ} (hkd : k ≤ d) :
    (boxReboxingFactor k : ℝ) ≤ Real.exp (((d : ℝ) + 2) ^ 3) := by
  have hfactor :
      (boxReboxingFactor k : ℝ) ≤
        ((4 * k + 1 : ℕ) : ℝ) ^ ((k + 2) * k) := by
    exact_mod_cast boxReboxingFactor_le_pow k
  have hexpOne : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h ⊢
    exact h
  have hexpTwo : (4 : ℝ) ≤ Real.exp 2 := by
    rw [(by norm_num : (2 : ℝ) = 1 + 1), Real.exp_add]
    nlinarith [Real.exp_pos 1]
  have hexpK : (k : ℝ) + 1 ≤ Real.exp k := by
    simpa using Real.add_one_le_exp (k : ℝ)
  have hbase : ((4 * k + 1 : ℕ) : ℝ) ≤ Real.exp ((k : ℝ) + 2) := by
    rw [Real.exp_add]
    have hmul := mul_le_mul hexpK hexpTwo (by positivity) (by positivity)
    push_cast
    nlinarith
  refine hfactor.trans ((pow_le_pow_left₀ (by positivity) hbase _).trans ?_)
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hkdR : (k : ℝ) ≤ d := by exact_mod_cast hkd
  push_cast
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k)
    (sq_nonneg ((k : ℝ) + 2)),
    pow_le_pow_left₀ (by positivity) (by linarith : (k : ℝ) + 2 ≤ d + 2) 3]

/-- The complete cost of one simultaneous quotient step is cubic-exponential in the current
dimension. -/
lemma saturated_quotient_factor_le_exp_cube {r d : ℕ} (hrd : r ≤ d) :
    (boxReboxingFactor (d - r) : ℝ) *
        ((2 * (r : ℝ) + 4) * (2 * (3 * (r : ℝ) + 1) + 1)) ^ d ≤
      Real.exp (13 * ((d : ℝ) + 2) ^ 3) := by
  have hrR : (r : ℝ) ≤ d := by exact_mod_cast hrd
  have hbase : (((2 * r + 4) * (2 * (3 * r + 1) + 1) : ℕ) : ℝ) ≤
      12 * ((d : ℝ) + 2) ^ 2 := by
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) r, Nat.cast_nonneg (α := ℝ) d,
      sq_nonneg ((d : ℝ) - r)]
  have hrebox := boxReboxingFactor_le_exp_cube (Nat.sub_le d r)
  have hpoly := poly_pow_le_exp_cube
    (show (0 : ℝ) ≤ (((2 * r + 4) * (2 * (3 * r + 1) + 1) : ℕ) : ℝ) by positivity)
    hbase
  push_cast at hpoly
  apply (mul_le_mul hrebox hpoly (by positivity) (by positivity)).trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

/-- Scaling the lengths by two and checking saturation both fit into one cubic exponential. -/
lemma saturation_room_factor_le_exp_cube (d : ℕ) :
    (2 * (3 * (d : ℝ)) + 1) ^ d * (2 : ℝ) ^ d ≤
      Real.exp (13 * ((d : ℝ) + 2) ^ 3) := by
  have hbase : (((2 * (3 * d) + 1 : ℕ) : ℝ)) ≤ 12 * ((d : ℝ) + 2) ^ 2 := by
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) d, sq_nonneg ((d : ℝ) + 2)]
  have hsat := poly_pow_le_exp_cube
    (show (0 : ℝ) ≤ ((2 * (3 * d) + 1 : ℕ) : ℝ) by positivity) hbase
  push_cast at hsat
  apply (mul_le_mul hsat (two_pow_le_exp d) (by positivity) (by positivity)).trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

/-- A cubic cost at each strict dimension drop telescopes inside a quartic budget. -/
lemma cube_step_le_fourth_difference {A : ℝ} (hA : 0 ≤ A) {e d : ℕ} (hed : e < d) :
    A * ((e : ℝ) + 2) ^ 4 + A * ((d : ℝ) + 2) ^ 3 ≤
      A * ((d : ℝ) + 2) ^ 4 := by
  have heNat : e + 2 ≤ d + 1 := by omega
  have he : (e : ℝ) + 2 ≤ (d : ℝ) + 1 := by exact_mod_cast heNat
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have he0 : (0 : ℝ) ≤ (e : ℝ) + 2 := by positivity
  have hpow : ((e : ℝ) + 2) ^ 4 ≤ ((d : ℝ) + 1) ^ 4 :=
    pow_le_pow_left₀ he0 he 4
  have hdiff : ((d : ℝ) + 1) ^ 4 + ((d : ℝ) + 2) ^ 3 ≤
      ((d : ℝ) + 2) ^ 4 := by
    nlinarith [sq_nonneg ((d : ℝ) + 1), mul_nonneg hd0 (sq_nonneg ((d : ℝ) + 1))]
  nlinarith [mul_le_mul_of_nonneg_left hpow hA, mul_le_mul_of_nonneg_left hdiff hA]

/-! ## The successive minima of the relation lattice

The coefficient box of a progression is the integer box of half-widths `length i - 1`, so the
relation lattice `GAP.relations` has successive minima with respect to it. This section reads the
geometry of numbers of `Chang.GeometryOfNumbers` and the lattice point count of
`Chang.BoxLatticePoints` through that box, which is the form in which the rank reduction of
properization consumes them.

The fact that drives the saturated quotient is that 2-properness is implied by `3 < λ₁`, which is
`GAP.twoProper_of_three_lt_relationMinimum`. -/

end

end ChangFreimanRuzsa
