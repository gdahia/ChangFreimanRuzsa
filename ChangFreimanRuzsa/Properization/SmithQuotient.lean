/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.BoxLatticePoints
public import ChangFreimanRuzsa.Lattice
public import ChangFreimanRuzsa.Properization.Relations
public import ChangFreimanRuzsa.LatticeBox.GaugeBox
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.TensorProduct.Pi
import ChangFreimanRuzsa.ConvexGeometry
import ChangFreimanRuzsa.LatticeBox.GaugeInduction
import ChangFreimanRuzsa.Properization.SaturatedSpan

/-! # Quotients of the coefficient lattice by a saturated span

The properization of a GAP divides the coefficient lattice $\mathbb{Z}^d$ by the saturated span of
its short relations. Every Smith coefficient of a saturated submodule is nonzero, so a Smith normal
form adapted to it splits a basis of $\mathbb{Z}^d$ into a basis of the submodule and free
coordinates on the quotient. The base change of that basis to $\mathbb{R}$ gives the real-linear
projection that extends these coordinates.

## Main definitions

* `smithQuotientMap`: the integral coordinates on the quotient given by a Smith normal form.
* `smithRealQuotientMap`: the real-linear map that extends them.
* `GAP.smithQuotientStep`: the steps of a GAP on the free coordinates.

## Main statements

* `exists_proper_gap_image_realBox`: the integer points of the image of a box under a
  surjective integral projection lie in a proper GAP of comparable size.
* `smithQuotientMap_eq_zero_iff` and `smithRealQuotientMap_eq_zero_iff`: the kernels of the
  quotient maps are the saturated span and its real span.
* `GAP.stepHom_smithQuotientMap`: if the saturated span consists of relations, the step
  homomorphism factors through the quotient coordinates.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open scoped Topology

noncomputable section

/-- A surjective real projection of an integral box with positive half-widths is a neighborhood
of the origin. -/
lemma image_realBox_mem_nhds_of_surjective {d s : ℕ} {m : Fin d → ℕ}
    (hm : ∀ i, 0 < m i) {π : (Fin d → ℝ) →ₗ[ℝ] (Fin s → ℝ)}
    (hπ : Function.Surjective π) :
    π '' BoxLattice.realBox m ∈ 𝓝 (0 : Fin s → ℝ) := by
  rw [← map_zero π]
  exact (LinearMap.isOpenMap_of_finiteDimensional π hπ).image_mem_nhds
    (BoxLattice.realBox_mem_nhds hm)

/-- The projected standard lattice points of a positive coordinate box span the target of every
surjective integral projection. -/
lemma span_image_realBox_inter_standardLattice_eq_top {d s : ℕ} {m : Fin d → ℕ}
    (hm : ∀ i, 0 < m i) {π : (Fin d → ℝ) →ₗ[ℝ] (Fin s → ℝ)} {πz : (Fin d → ℤ) →+ (Fin s → ℤ)}
    (hcast : ∀ v, π (intVectorToReal v) = intVectorToReal (πz v))
    (hπ : Function.Surjective π) :
    Submodule.span ℝ
      ((π '' BoxLattice.realBox m) ∩
        ((⊤ : AddSubgroup (Fin s → ℤ)).map intVectorToReal : Set (Fin s → ℝ))) = ⊤ := by
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
      simpa [Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero] using hm i
    · simp [Pi.basisFun_apply, hji]
  · refine AddSubgroup.mem_map.mpr
      ⟨πz (Pi.single i 1), Set.mem_univ _, ?_⟩
    rw [← hcast]
    congr 1
    ext j
    simp [Pi.basisFun_apply, Pi.single_apply]

/-- The integer points `D` of the image of a positive coordinate box under a surjective integral
projection $\pi : \mathbb{R}^d \to \mathbb{R}^s$ lie in a proper GAP of dimension at most $s$ with
at most `latticeBoxFactor s * D.card` elements. -/
lemma exists_proper_gap_image_realBox {d s : ℕ} {m : Fin d → ℕ}
    (hm : ∀ i, 0 < m i) {π : (Fin d → ℝ) →ₗ[ℝ] (Fin s → ℝ)} {πz : (Fin d → ℤ) →+ (Fin s → ℤ)}
    (hcast : ∀ v, π (intVectorToReal v) = intVectorToReal (πz v))
    (hπ : Function.Surjective π) {D : Finset (Fin s → ℤ)}
    (hD : ∀ v, v ∈ D ↔ intVectorToReal v ∈ π '' BoxLattice.realBox m) :
    ∃ P : GAP (Fin s → ℤ), P.Proper ∧ D ⊆ P.carrier ∧ P.dim ≤ s ∧
      P.carrier.card ≤ latticeBoxFactor s * D.card :=
  exists_proper_gap_of_convex_body ((BoxLattice.convex_realBox m).linear_image π)
    ((BoxLattice.isCompact_realBox m).image (LinearMap.continuous_of_finiteDimensional π))
    (image_realBox_mem_nhds_of_surjective hm hπ)
    (ConvexGeometry.neg_mem_image fun _ ↦ BoxLattice.neg_mem_realBox)
    (span_image_realBox_inter_standardLattice_eq_top hm hcast hπ) hD

/-! ## Real bases from integral bases -/

/-- An integral basis of `ℤ ^ d`, extended to a real basis of `ℝ ^ d`. -/
def basisToReal {d : ℕ} (b : Module.Basis (Fin d) ℤ (Fin d → ℤ)) :
    Module.Basis (Fin d) ℝ (Fin d → ℝ) :=
  (b.baseChange ℝ).map (TensorProduct.piScalarRight ℤ ℝ ℝ (Fin d))

lemma basisToReal_apply {d : ℕ} (b : Module.Basis (Fin d) ℤ (Fin d → ℤ)) (i : Fin d) :
    basisToReal b i = intVectorToReal (b i) := by
  ext k
  simp [basisToReal, Algebra.smul_def]

lemma basisToReal_repr_intCast {d : ℕ} (b : Module.Basis (Fin d) ℤ (Fin d → ℤ))
    (v : Fin d → ℤ) (i : Fin d) :
    (basisToReal b).repr (intVectorToReal v) i = b.repr v i := by
  have hv : intVectorToReal v = TensorProduct.piScalarRight ℤ ℝ ℝ (Fin d) (1 ⊗ₜ[ℤ] v) := by
    ext k
    simp [Algebra.smul_def]
  rw [hv, basisToReal, Module.Basis.map_repr, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, Module.Basis.baseChange_repr_tmul]
  simp [Algebra.smul_def]

/-! ## Smith normal forms of a saturated span -/

/-- An enumeration of the indices of the ambient Smith basis outside the range of `f`. -/
def smithComplementEquiv {d n : ℕ} (f : Fin n ↪ Fin d) :
    Fin (d - n) ≃ {i : Fin d // i ∉ Set.range f} :=
  Fintype.equivOfCardEq (by
    simp [Fintype.card_subtype_compl, -Set.mem_range, Set.card_range_of_injective f.injective])

/-- A finitely supported function vanishing at the indices enumerated by `smithComplementEquiv f`
is supported in the range of `f`. -/
lemma support_subset_range_of_apply_smithComplementEquiv_eq_zero {d n : ℕ} {R : Type*} [Zero R]
    {f : Fin n ↪ Fin d} {g : Fin d →₀ R} (hg : ∀ k, g (smithComplementEquiv f k) = 0) :
    ↑g.support ⊆ Set.range f := by
  intro i hi
  by_contra hf
  obtain ⟨k, hk⟩ := (smithComplementEquiv f).surjective ⟨i, hf⟩
  exact Finsupp.mem_support_iff.mp hi (by simpa [hk] using hg k)

variable {d n : ℕ} {S : Finset (Fin d → ℤ)}
  (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin d) n)

/-- The vectors of the ambient Smith basis indexed by the range of `snf.f` lie in the saturated
span. -/
lemma smithBasis_mem_saturatedSpan (i : Fin n) : snf.bM (snf.f i) ∈ saturatedSpan S := by
  refine mem_saturatedSpan_of_zsmul_mem (c := snf.a i) ?_ ?_
  · intro ha
    apply snf.bN.ne_zero i
    ext1
    simp [snf.snf, ha]
  · rw [← snf.snf]
    exact (snf.bN i).prop

/-- The integral coordinates on the quotient by the saturated span given by a Smith normal form. -/
def smithQuotientMap : (Fin d → ℤ) →+ (Fin (d - n) → ℤ) where
  toFun x k := snf.bM.repr x (smithComplementEquiv snf.f k)
  map_zero' := by
    ext k
    simp
  map_add' x y := by
    ext k
    simp

/-- The lift with zero coordinates along the saturated span. -/
def smithQuotientLift (y : Fin (d - n) → ℤ) : Fin d → ℤ :=
  ∑ k, y k • snf.bM (smithComplementEquiv snf.f k)

lemma smithQuotientMap_lift (y : Fin (d - n) → ℤ) :
    smithQuotientMap snf (smithQuotientLift snf y) = y := by
  ext i
  simp only [smithQuotientMap, smithQuotientLift, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sum,
    map_zsmul, Module.Basis.repr_self]
  simp [Finsupp.single_apply, Subtype.val_inj]

lemma smithQuotientMap_eq_zero_iff (x : Fin d → ℤ) :
    smithQuotientMap snf x = 0 ↔ x ∈ saturatedSpan S := by
  constructor
  · intro hx
    refine Submodule.span_le.mpr ?_ (snf.bM.mem_span_image.mpr
      (support_subset_range_of_apply_smithComplementEquiv_eq_zero (congr_fun hx)))
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact smithBasis_mem_saturatedSpan snf i
  · intro hx
    ext k
    exact snf.repr_eq_zero_of_notMem_range ⟨x, hx⟩ (smithComplementEquiv snf.f k).prop

lemma smithQuotientMap_eq_iff (x y : Fin d → ℤ) :
    smithQuotientMap snf x = smithQuotientMap snf y ↔ x - y ∈ saturatedSpan S := by
  rw [← sub_eq_zero, ← map_sub, smithQuotientMap_eq_zero_iff]

/-! ## The real quotient map -/

/-- The real-linear map that extends `smithQuotientMap`. -/
def smithRealQuotientMap : (Fin d → ℝ) →ₗ[ℝ] (Fin (d - n) → ℝ) :=
  LinearMap.pi fun k ↦ (basisToReal snf.bM).coord (smithComplementEquiv snf.f k)

/-- On integer vectors, the real quotient map is the cast of `smithQuotientMap`. -/
lemma smithRealQuotientMap_intCast (v : Fin d → ℤ) :
    smithRealQuotientMap snf (intVectorToReal v) =
      intVectorToReal (smithQuotientMap snf v) := by
  ext k
  simp [smithRealQuotientMap, basisToReal_repr_intCast, smithQuotientMap]

lemma smithRealQuotientMap_surjective : Function.Surjective (smithRealQuotientMap snf) := by
  intro y
  use ∑ k, y k • basisToReal snf.bM (smithComplementEquiv snf.f k)
  ext i
  simp [smithRealQuotientMap, Finsupp.single_apply, Subtype.val_inj]

/-- The kernel of the real quotient map is the real span of $S$. -/
lemma smithRealQuotientMap_eq_zero_iff (x : Fin d → ℝ) :
    smithRealQuotientMap snf x = 0 ↔ x ∈ integerGeneratedSubspace S := by
  constructor
  · intro hx
    refine Submodule.span_le.mpr ?_ ((basisToReal snf.bM).mem_span_image.mpr
      (support_subset_range_of_apply_smithComplementEquiv_eq_zero (congr_fun hx)))
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [basisToReal_apply]
    exact smithBasis_mem_saturatedSpan snf i
  · intro hx
    refine LinearMap.mem_ker.mp ((Submodule.span_le.mpr ?_ :
      integerGeneratedSubspace S ≤ LinearMap.ker (smithRealQuotientMap snf)) hx)
    rintro _ ⟨v, hv, rfl⟩
    change smithRealQuotientMap snf (intVectorToReal v) = 0
    rw [smithRealQuotientMap_intCast, (smithQuotientMap_eq_zero_iff snf v).mpr
      (subset_saturatedSpan S hv), map_zero]

/-! ## Steps on the quotient -/

variable {G : Type*} [AddCommGroup G]

namespace GAP

/-- The steps of a GAP on the free coordinates of a Smith normal form. -/
def smithQuotientStep (P : GAP G) {n : ℕ} {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    Fin (P.dim - n) → G :=
  fun k ↦ stepHom P (snf.bM (smithComplementEquiv snf.f k))

/-- If the saturated span consists of relations, the step homomorphism factors through the Smith
quotient coordinates. -/
lemma stepHom_smithQuotientMap (P : GAP G) {n : ℕ} {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n)
    (hrel : (saturatedSpan S).toAddSubgroup ≤ P.relations) (x : Fin P.dim → ℤ) :
    stepsHom (P.smithQuotientStep snf) (smithQuotientMap snf x) = stepHom P x := by
  have hlift : stepHom P (smithQuotientLift snf (smithQuotientMap snf x)) = stepHom P x := by
    rw [← sub_eq_zero, ← map_sub]
    exact hrel ((smithQuotientMap_eq_iff snf _ _).mp (smithQuotientMap_lift snf _))
  rw [← hlift, stepsHom_apply, smithQuotientLift, map_sum]
  simp_rw [smithQuotientStep, map_zsmul]

end GAP

end

end ChangFreimanRuzsa
