/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GAP.Basic
public import ChangFreimanRuzsa.GeometryOfNumbers.SymmetricBody
public import Mathlib.LinearAlgebra.TensorProduct.Pi
import Aesop.Main
import ChangFreimanRuzsa.GeometryOfNumbers.ProjectionVolume
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Quotients of a symmetric body by a lattice relation

Let `K ⊆ ℝ ^ (m + 1)` be a full symmetric body and `φ : (Fin (m + 1) → ℤ) →+ G` a homomorphism into
an abelian group in which the multiples `n • a` with `n < N` of every nonzero `a` are distinct. If
`φ` is not injective on the integer points of `s • K`, then `φ` has a nonzero relation `x` in
`(2 * s) • K`. Write `x = k • b i` for a basis `b` of `ℤ ^ (m + 1)`. If `K` has fewer than `N`
integer points in `(2 * s) • K`, then `φ (b i) = 0`, since the multiples `j • b i` with `j ≤ |k|`
lie in `(2 * s) • K`. So `φ` factors through the coordinates in `b` other than the `i`-th. These
coordinates map `K` onto a full symmetric body `K' ⊆ ℝ ^ m`, and since `(2 * s)⁻¹ • b i ∈ K` the
volume of `K'` is at most `s * (m + 1) ^ 2 * vol K`. This is the step of Lemma 2.2 of Green's notes
*Progressions and convex geometry*.

## Main definitions

* `basisToReal b`: an integral basis of `ℤ ^ d`, extended to a real basis of `ℝ ^ d`.

## Main statements

* `exists_quotient_of_not_injOn`: the quotient step.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open MeasureTheory Module Set
open scoped Pointwise

noncomputable section

/-! ## Real bases from integral bases -/

/-- An integral basis of `ℤ ^ d`, extended to a real basis of `ℝ ^ d`. -/
def basisToReal {d : ℕ} (b : Basis (Fin d) ℤ (Fin d → ℤ)) : Basis (Fin d) ℝ (Fin d → ℝ) :=
  (b.baseChange ℝ).map (TensorProduct.piScalarRight ℤ ℝ ℝ (Fin d))

lemma basisToReal_apply {d : ℕ} (b : Basis (Fin d) ℤ (Fin d → ℤ)) (i : Fin d) :
    basisToReal b i = intVectorToReal (b i) := by
  ext k
  simp [basisToReal, Algebra.smul_def]

lemma basisToReal_repr_intCast {d : ℕ} (b : Basis (Fin d) ℤ (Fin d → ℤ)) (v : Fin d → ℤ)
    (i : Fin d) : (basisToReal b).repr (intVectorToReal v) i = b.repr v i := by
  have hv : intVectorToReal v = TensorProduct.piScalarRight ℤ ℝ ℝ (Fin d) (1 ⊗ₜ[ℤ] v) := by
    ext k
    simp [Algebra.smul_def]
  rw [hv, basisToReal, Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    Basis.baseChange_repr_tmul]
  simp [Algebra.smul_def]

/-- The real extension of an integral basis has determinant `±1`. -/
lemma abs_det_basisToReal {d : ℕ} (b : Basis (Fin d) ℤ (Fin d → ℤ)) :
    |(Pi.basisFun ℝ (Fin d)).det (basisToReal b)| = 1 := by
  have h : (Pi.basisFun ℝ (Fin d)).det (basisToReal b) = ((Pi.basisFun ℤ (Fin d)).det b : ℝ) := by
    rw [Pi.basisFun_det_apply, Pi.basisFun_det_apply, ← eq_intCast (Int.castRingHom ℝ),
      RingHom.map_det]
    congr 1
    ext i j
    simp [basisToReal_apply]
  rw [h, ← Int.cast_abs, Int.isUnit_iff_abs_eq.1 ((Pi.basisFun ℤ (Fin d)).isUnit_det b),
    Int.cast_one]

/-- Taking coordinates in a basis `b` scales volumes by `|det b|⁻¹`. -/
private lemma volume_image_equivFun {d : ℕ} (b : Basis (Fin d) ℝ (Fin d → ℝ))
    (K : Set (Fin d → ℝ)) :
    volume (b.equivFun '' K) = ENNReal.ofReal |((Pi.basisFun ℝ (Fin d)).det b)⁻¹| * volume K := by
  have h : LinearMap.det b.equivFun.symm.toLinearMap = (Pi.basisFun ℝ (Fin d)).det b := by
    rw [Pi.basisFun_det_apply, ← Matrix.det_transpose, ← LinearMap.det_toLin']
    congr 1
    ext c i
    simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Basis.equivFun_symm_apply, mul_comm]
  rw [b.equivFun.image_eq_preimage_symm, ← h]
  exact Measure.addHaar_preimage_linearMap volume (f := b.equivFun.symm.toLinearMap)
    (by rw [h]; exact ((Pi.basisFun ℝ (Fin d)).isUnit_det b).ne_zero) K

/-- Coordinates in an integral basis preserve volume. -/
private lemma volume_image_equivFun_basisToReal {d : ℕ} (b : Basis (Fin d) ℤ (Fin d → ℤ))
    (K : Set (Fin d → ℝ)) : volume ((basisToReal b).equivFun '' K) = volume K := by
  rw [volume_image_equivFun, abs_inv, abs_det_basisToReal, inv_one, ENNReal.ofReal_one, one_mul]

/-! ## The coordinates other than one -/

variable {m : ℕ} (b : Basis (Fin (m + 1)) ℤ (Fin (m + 1) → ℤ)) (i : Fin (m + 1))

/-- The coordinates in the basis `b` other than the `i`-th. -/
private def basisQuotient : (Fin (m + 1) → ℤ) →+ (Fin m → ℤ) :=
  (LinearMap.pi fun j ↦ b.coord (i.succAbove j)).toAddMonoidHom

/-- The real-linear map that extends `basisQuotient b i`. -/
private def realBasisQuotient : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
  LinearMap.pi fun j ↦ (basisToReal b).coord (i.succAbove j)

private lemma realBasisQuotient_apply (x : Fin (m + 1) → ℝ) :
    realBasisQuotient b i x = i.removeNth ((basisToReal b).equivFun x) :=
  rfl

/-- On integer vectors, the real map is the cast of `basisQuotient b i`. -/
private lemma realBasisQuotient_intCast (v : Fin (m + 1) → ℤ) :
    realBasisQuotient b i (intVectorToReal v) = intVectorToReal (basisQuotient b i v) := by
  ext j
  simp [realBasisQuotient, basisQuotient, basisToReal_repr_intCast]

private lemma realBasisQuotient_surjective : Function.Surjective (realBasisQuotient b i) := by
  intro y
  refine ⟨(basisToReal b).equivFun.symm (i.insertNth 0 y), ?_⟩
  rw [realBasisQuotient_apply, LinearEquiv.apply_symm_apply]
  ext j
  simp [Fin.removeNth]

/-- If `φ (b i) = 0`, then `φ` factors through `basisQuotient b i`. -/
private lemma stepsHom_basisQuotient {G : Type*} [AddCommGroup G] {φ : (Fin (m + 1) → ℤ) →+ G}
    (hφ : φ (b i) = 0) (v : Fin (m + 1) → ℤ) :
    stepsHom (fun j ↦ φ (b (i.succAbove j))) (basisQuotient b i v) = φ v := by
  conv_rhs => rw [← b.sum_repr v]
  simp_rw [map_sum, map_zsmul]
  rw [Fin.sum_univ_succAbove _ i, hφ, smul_zero, zero_add, stepsHom_apply]
  rfl

/-- The coordinates other than the `i`-th map a symmetric convex compact set `K` containing
`h • b i` onto a set of volume at most `(m + 1) ^ 2 / (2 * h) * vol K`. -/
private lemma volume_image_realBasisQuotient_le {K : Set (Fin (m + 1) → ℝ)} (hK : Convex ℝ K)
    (hKc : IsCompact K) (hsymm : ∀ x ∈ K, -x ∈ K) {h : ℝ} (hh : 0 < h)
    (hi : h • basisToReal b i ∈ K) :
    volume (realBasisQuotient b i '' K) ≤ ENNReal.ofReal ((m + 1) ^ 2 / (2 * h)) * volume K := by
  set C := (basisToReal b).equivFun
  have hC : realBasisQuotient b i '' K = i.removeNth '' (C '' K) := by
    rw [image_image]
    rfl
  rw [hC, ← volume_image_equivFun_basisToReal b K]
  refine volume_image_removeNth_le (hK.linear_image C.toLinearMap)
    (hKc.image C.toContinuousLinearEquiv.continuous) ?_ i hh ⟨_, hi, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨-x, hsymm x hx, map_neg C x⟩
  · ext j
    simp [C, Pi.single_apply, Finsupp.single_apply, eq_comm]

/-- The image of a full symmetric body under `realBasisQuotient b i` is a full symmetric body. -/
private lemma IsFullSymmetricBody.image_realBasisQuotient {K : Set (Fin (m + 1) → ℝ)}
    (hK : IsFullSymmetricBody K) : IsFullSymmetricBody (realBasisQuotient b i '' K) where
  convex := hK.convex.linear_image _
  isCompact := hK.isCompact.image (LinearMap.continuous_of_finiteDimensional _)
  neg_mem := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨-x, hK.neg_mem x hx, map_neg _ x⟩
  nonempty := hK.nonempty.image _
  span_latticePoints := by
    refine eq_top_mono ?_ (LinearMap.range_eq_top.2 (realBasisQuotient_surjective b i))
    rw [LinearMap.range_eq_map, ← hK.span_latticePoints, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨basisQuotient b i v,
      ⟨_, hv, realBasisQuotient_intCast b i v⟩, (realBasisQuotient_intCast b i v).symm⟩

/-- `basisQuotient b i` maps the integer points of `K` to integer points of the image of `K`. -/
private lemma basisQuotient_mem_latticePoints {K : Set (Fin (m + 1) → ℝ)} {v : Fin (m + 1) → ℤ}
    (hv : v ∈ latticePoints K) :
    basisQuotient b i v ∈ latticePoints (realBasisQuotient b i '' K) :=
  ⟨_, hv, realBasisQuotient_intCast b i v⟩

end

/-! ## The quotient step -/

section Step

variable {G : Type*} [AddCommGroup G] {m N : ℕ}

/-- A nonzero integer vector is a multiple of a vector of some basis of `ℤ ^ d`. -/
private lemma exists_basis_eq_zsmul {d : ℕ} {x : Fin d → ℤ} (hx : x ≠ 0) :
    ∃ (b : Basis (Fin d) ℤ (Fin d → ℤ)) (i : Fin d) (k : ℤ), x = k • b i := by
  obtain ⟨n, snf⟩ := (Submodule.span ℤ (range fun _ : Fin 1 ↦ x)).smithNormalForm
    (Pi.basisFun ℤ (Fin d))
  obtain rfl : n = 1 := by
    rw [← Fintype.card_fin n, ← finrank_eq_card_basis snf.bN,
      finrank_span_eq_card (linearIndependent_unique_iff.2 hx), Fintype.card_fin]
  have hxN : x ∈ Submodule.span ℤ (range fun _ : Fin 1 ↦ x) := Submodule.subset_span ⟨0, rfl⟩
  refine ⟨snf.bM, snf.f 0, snf.bN.repr ⟨x, hxN⟩ 0 * snf.a 0, ?_⟩
  have h := congr_arg Subtype.val (snf.bN.sum_repr ⟨x, hxN⟩)
  rw [Fin.sum_univ_one] at h
  rw [mul_smul, ← snf.snf]
  exact h.symm

/-- If `k • a = 0` for some `k ≠ 0` with `|k| < N`, and the multiples `n • a` with `n < N` of every
nonzero `a` are distinct, then `a = 0`. -/
private lemma eq_zero_of_zsmul_eq_zero (hG : ∀ a : G, a ≠ 0 → InjOn (fun n : ℕ ↦ n • a) (Iio N))
    {a : G} {k : ℤ} (hk : k ≠ 0) (hkN : k.natAbs < N) (hka : k • a = 0) : a = 0 := by
  by_contra ha
  have hk' : k.natAbs • a = 0 := by
    rcases k.natAbs_eq with h | h
    · rwa [h, natCast_zsmul] at hka
    · rwa [h, neg_smul, neg_eq_zero, natCast_zsmul] at hka
  exact Int.natAbs_ne_zero.2 hk (hG a ha hkN (lt_of_le_of_lt (Nat.zero_le _) hkN)
    (by simpa using hk'))

/-- If `φ` is not injective on the integer points of `s • K`, it has a nonzero relation among the
integer points of `(2 * s) • K`. -/
private lemma exists_ne_zero_mem_latticePoints_of_not_injOn {d : ℕ} {K : Set (Fin d → ℝ)}
    (hK : IsFullSymmetricBody K) {s : ℝ} {φ : (Fin d → ℤ) →+ G}
    (hφ : ¬ InjOn φ (latticePoints (s • K))) :
    ∃ x ≠ 0, x ∈ latticePoints ((2 * s) • K) ∧ φ x = 0 := by
  simp only [InjOn, not_forall] at hφ
  obtain ⟨u, hu, v, hv, huv, hne⟩ := hφ
  refine ⟨u - v, sub_ne_zero.2 hne, ?_, by rw [map_sub, huv, sub_self]⟩
  rw [mem_latticePoints, map_sub, mul_smul,
    ← sub_self_eq_two_smul (hK.convex.smul s) (neg_mem_smul_set hK.neg_mem s)]
  exact sub_mem_sub hu hv

/-- If a multiple `k • y` of a nonzero integer vector lies in a symmetric convex bounded set `L`,
then so do `j • y` for `j ≤ |k|`, so `L` has more than `|k|` integer points. -/
private lemma natAbs_lt_ncard_latticePoints {d : ℕ} {L : Set (Fin d → ℝ)} (hL : Convex ℝ L)
    (hLb : Bornology.IsBounded L) (hsymm : ∀ x ∈ L, -x ∈ L) {y : Fin d → ℤ} (hy : y ≠ 0) {k : ℤ}
    (hk : k • y ∈ latticePoints L) : k.natAbs < (latticePoints L).ncard := by
  have h := ncard_le_ncard_of_injOn (fun j : ℕ ↦ (j : ℤ) • y)
    (s := (Finset.range (k.natAbs + 1) : Set ℕ)) ?_ ?_ (finite_latticePoints hLb)
  · rwa [ncard_coe_finset, Finset.card_range, Nat.succ_le_iff] at h
  · intro j hj
    rw [Finset.coe_range, mem_Iio, Nat.lt_succ_iff] at hj
    rcases eq_or_ne k 0 with rfl | hk0
    · obtain rfl : j = 0 := by simpa using hj
      simpa using hk
    rw [mem_latticePoints, map_zsmul]
    convert smul_mem_of_abs_le_one hL hsymm hk (t := (j : ℝ) / k) ?_ using 1
    · rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ, smul_smul,
        div_mul_cancel₀ _ (by exact_mod_cast hk0)]
      simp
    · rw [abs_div, div_le_one (by positivity), Nat.abs_cast, ← Int.cast_abs, Int.abs_eq_natAbs,
        Int.cast_natCast]
      exact_mod_cast hj
  · intro j _ j' _ h
    exact Nat.cast_injective (smul_left_injective ℤ hy h)

/-- **The quotient step.** Let `K ⊆ ℝ ^ (m + 1)` be a full symmetric body, `0 < s`, and
`φ : (Fin (m + 1) → ℤ) →+ G` not injective on the integer points of `s • K`. If the multiples
`n • a` with `n < N` of every nonzero `a` are distinct and `(2 * s) • K` has fewer than `N` integer
points, then `φ` factors through a full symmetric body `K' ⊆ ℝ ^ m`: there is
`ψ : (Fin m → ℤ) →+ G` with `φ '' latticePoints K ⊆ ψ '' latticePoints K'`, and
`vol K' ≤ s * (m + 1) ^ 2 * vol K`. -/
lemma exists_quotient_of_not_injOn (hG : ∀ a : G, a ≠ 0 → InjOn (fun n : ℕ ↦ n • a) (Iio N))
    {K : Set (Fin (m + 1) → ℝ)} (hK : IsFullSymmetricBody K) {s : ℝ} (hs : 0 < s)
    (hN : (latticePoints ((2 * s) • K)).ncard < N) {φ : (Fin (m + 1) → ℤ) →+ G}
    (hφ : ¬ InjOn φ (latticePoints (s • K))) :
    ∃ (K' : Set (Fin m → ℝ)) (ψ : (Fin m → ℤ) →+ G), IsFullSymmetricBody K' ∧
      φ '' latticePoints K ⊆ ψ '' latticePoints K' ∧
      volume.real K' ≤ s * (m + 1) ^ 2 * volume.real K := by
  obtain ⟨x, hx, hxK, hφx⟩ := exists_ne_zero_mem_latticePoints_of_not_injOn hK hφ
  obtain ⟨b, i, k, rfl⟩ := exists_basis_eq_zsmul hx
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hx
  have hs2 : 0 < 2 * s := by positivity
  have hbK : (2 * s)⁻¹ • basisToReal b i ∈ K := by
    rw [← mem_smul_set_iff_inv_smul_mem₀ hs2.ne', basisToReal_apply]
    convert smul_mem_of_abs_le_one (hK.convex.smul _) (neg_mem_smul_set hK.neg_mem _) hxK
      (t := (k : ℝ)⁻¹) ?_ using 1
    · rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hk),
        one_smul]
    · rw [abs_inv]
      exact inv_le_one_of_one_le₀ (by exact_mod_cast Int.one_le_abs hk)
  have hbi : φ (b i) = 0 :=
    eq_zero_of_zsmul_eq_zero hG hk ((natAbs_lt_ncard_latticePoints (hK.convex.smul _)
      (hK.isCompact.smul _).isBounded (neg_mem_smul_set hK.neg_mem _) (b.ne_zero i) hxK).trans hN)
      (by rwa [← map_zsmul])
  refine ⟨realBasisQuotient b i '' K, stepsHom fun j ↦ φ (b (i.succAbove j)),
    hK.image_realBasisQuotient b i, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact ⟨_, basisQuotient_mem_latticePoints b i hv, stepsHom_basisQuotient b i hbi v⟩
  · have h := volume_image_realBasisQuotient_le b i hK.convex hK.isCompact hK.neg_mem
      (inv_pos.2 hs2) hbK
    rw [(by field_simp : (m + 1 : ℝ) ^ 2 / (2 * (2 * s)⁻¹) = s * (m + 1) ^ 2)] at h
    have h' := ENNReal.toReal_mono (by finiteness [hK.volume_ne_top]) h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h'

end Step

end ChangFreimanRuzsa
