/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GeometryOfNumbers.LatticePointCount
import Aesop.Main

/-!
# Symmetric convex bodies whose lattice points span

A set `K ⊆ ℝ ^ n` is a full symmetric body if it is convex, compact and symmetric about the origin
and its integer points span `ℝ ^ n`. These are the bodies of the convex progressions of Green's
notes *Progressions and convex geometry*. For such a body the number of integer points and the
volume are comparable:

* `IsFullSymmetricBody.ncard_latticePoints_le`: `#(latticePoints K) ≤ (1 + n / 2) ^ n * vol K`.
  The integer points of `K` contain a basis of `ℝ ^ n`, whose fundamental parallelepiped, centered
  at the origin, lies in `(n / 2) • K`. So every point of `ℝ ^ n` is an integer vector plus a point
  of `(n / 2) • K`, and its translates by the integer points of `K` lie in `(1 + n / 2) • K`.
* `volume_real_le_ncard_latticePoints_two_smul`: `vol K ≤ #(latticePoints (2 • K))` for a symmetric
  convex compact `K`, the theorem of van der Corput.

## Main definitions

* `IsFullSymmetricBody K`: `K` is convex, compact, symmetric and its integer points span.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open MeasureTheory Module
open scoped Pointwise

noncomputable section

variable {n : ℕ}

/-- A full symmetric body: a convex compact set `K ⊆ ℝ ^ n`, symmetric about the origin, whose
integer points span `ℝ ^ n`. -/
structure IsFullSymmetricBody (K : Set (Fin n → ℝ)) : Prop where
  convex : Convex ℝ K
  isCompact : IsCompact K
  neg_mem : ∀ x ∈ K, -x ∈ K
  nonempty : K.Nonempty
  span_latticePoints : Submodule.span ℝ (intVectorToReal '' latticePoints K) = ⊤

/-! ## Symmetric convex sets -/

section Symmetric

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {K : Set V}

private lemma zero_mem_of_neg_mem (hK : Convex ℝ K) (hsymm : ∀ x ∈ K, -x ∈ K) (hne : K.Nonempty) :
    (0 : V) ∈ K := by
  obtain ⟨x, hx⟩ := hne
  convert hK.add_smul_sub_mem hx (hsymm x hx) (t := 1 / 2) ⟨by norm_num, by norm_num⟩ using 1
  module

/-- A symmetric convex set containing the origin is balanced. -/
lemma smul_mem_of_abs_le_one (hK : Convex ℝ K) (hsymm : ∀ x ∈ K, -x ∈ K) {x : V} (hx : x ∈ K)
    {t : ℝ} (ht : |t| ≤ 1) : t • x ∈ K := by
  have h₀ := zero_mem_of_neg_mem hK hsymm ⟨x, hx⟩
  rcases le_total 0 t with h | h
  · exact hK.smul_mem_of_zero_mem h₀ hx ⟨h, by grind [abs_of_nonneg h]⟩
  · rw [← neg_neg t, neg_smul, ← smul_neg]
    exact hK.smul_mem_of_zero_mem h₀ (hsymm x hx) ⟨by linarith, by grind [abs_of_nonpos h]⟩

/-- A dilate of a symmetric set is symmetric. -/
lemma neg_mem_smul_set (hsymm : ∀ x ∈ K, -x ∈ K) (c : ℝ) : ∀ x ∈ c • K, -x ∈ c • K := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨-y, hsymm y hy, smul_neg c y⟩

omit [Module ℝ V] in
private lemma neg_set_eq_self (hsymm : ∀ x ∈ K, -x ∈ K) : -K = K :=
  Set.Subset.antisymm (fun x hx ↦ by simpa using hsymm _ hx) fun x hx ↦ by simpa using hsymm x hx

/-- For a symmetric convex set, `K - K = 2 • K`. -/
lemma sub_self_eq_two_smul (hK : Convex ℝ K) (hsymm : ∀ x ∈ K, -x ∈ K) : K - K = (2 : ℝ) • K := by
  rw [sub_eq_add_neg, neg_set_eq_self hsymm, ← one_add_one_eq_two,
    hK.add_smul zero_le_one zero_le_one, one_smul]

/-- A combination `∑ i, a i • w i` of `m` points of a symmetric convex set `K` with `|a i| ≤ 1 / 2`
lies in `(m / 2) • K`. -/
lemma sum_smul_mem_smul_of_abs_le (hK : Convex ℝ K) (hsymm : ∀ x ∈ K, -x ∈ K) (hne : K.Nonempty)
    {ι : Type*} [Fintype ι] {w : ι → V} (hw : ∀ i, w i ∈ K) {a : ι → ℝ}
    (ha : ∀ i, |a i| ≤ 1 / 2) : ∑ i, a i • w i ∈ (Fintype.card ι / 2 : ℝ) • K := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Set.zero_smul_set hne]
  have hcard : (0 : ℝ) < Fintype.card ι := mod_cast Fintype.card_pos
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (by positivity), Finset.smul_sum]
  have h := hK.sum_mem (t := Finset.univ) (w := fun _ ↦ (Fintype.card ι : ℝ)⁻¹)
    (z := fun i ↦ (2 * a i) • w i) (fun _ _ ↦ by positivity) (by simp [hcard.ne'])
    (fun i _ ↦ smul_mem_of_abs_le_one hK hsymm (hw i) (by grind [ha i]))
  convert h using 2 with i
  rw [smul_smul, smul_smul]
  congr 1
  field_simp

end Symmetric

lemma volume_real_smul {c : ℝ} (hc : 0 ≤ c) (K : Set (Fin n → ℝ)) :
    volume.real (c • K) = c ^ n * volume.real K := by
  rw [measureReal_def, Measure.addHaar_smul_of_nonneg _ hc, finrank_fin_fun, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hc n), measureReal_def]

namespace IsFullSymmetricBody

variable {K : Set (Fin n → ℝ)} (hK : IsFullSymmetricBody K)
include hK

lemma isBounded : Bornology.IsBounded K := hK.isCompact.isBounded

lemma volume_ne_top : volume K ≠ ⊤ := hK.isCompact.measure_lt_top.ne

lemma finite_latticePoints : (latticePoints K).Finite :=
  ChangFreimanRuzsa.finite_latticePoints hK.isBounded

lemma zero_mem : (0 : Fin n → ℝ) ∈ K := zero_mem_of_neg_mem hK.convex hK.neg_mem hK.nonempty

/-- A dilate `c • K` with `1 ≤ c` is again a full symmetric body. -/
lemma smul {c : ℝ} (hc : 1 ≤ c) : IsFullSymmetricBody (c • K) where
  convex := hK.convex.smul c
  isCompact := hK.isCompact.smul c
  neg_mem := neg_mem_smul_set hK.neg_mem c
  nonempty := hK.nonempty.smul_set
  span_latticePoints := by
    refine eq_top_mono (Submodule.span_mono (Set.image_mono fun v hv ↦ ?_)) hK.span_latticePoints
    refine ⟨c⁻¹ • intVectorToReal v, smul_mem_of_abs_le_one hK.convex hK.neg_mem hv ?_, ?_⟩
    · rw [abs_inv, abs_of_pos (by linarith)]
      exact inv_le_one_of_one_le₀ hc
    · simp [smul_smul, (by linarith : c ≠ 0)]

/-- The dilates of a full symmetric body are nested: `a • K ⊆ b • K` for `|a| ≤ |b|`. -/
lemma smul_subset_smul {a b : ℝ} (hab : |a| ≤ |b|) : a • K ⊆ b • K := by
  refine Balanced.smul_mono ?_ (by simpa using hab)
  rintro c hc _ ⟨x, hx, rfl⟩
  exact smul_mem_of_abs_le_one hK.convex hK.neg_mem hx (by simpa using hc)

/-- Every point of `ℝ ^ n` is an integer vector plus a point of `(n / 2) • K`. The integer points
of `K` contain a basis of `ℝ ^ n`; round the coordinates of the point in that basis. -/
private lemma exists_sub_mem_smul (x : Fin n → ℝ) :
    ∃ z : Fin n → ℤ, x - intVectorToReal z ∈ (n / 2 : ℝ) • K := by
  obtain ⟨B, hBsub, hBspan, hBli⟩ := exists_linearIndependent ℝ (intVectorToReal '' latticePoints K)
  let b : Basis B ℝ (Fin n → ℝ) :=
    Basis.mk hBli (by rw [Subtype.range_coe, hBspan, hK.span_latticePoints])
  have : Fintype B := FiniteDimensional.fintypeBasisIndex b
  have hcard : Fintype.card B = n := by rw [← finrank_eq_card_basis b, finrank_fin_fun]
  choose v hv using fun i : B ↦ hBsub i.2
  refine ⟨∑ i, round (b.repr x i) • v i, ?_⟩
  have hx : x - intVectorToReal (∑ i, round (b.repr x i) • v i) =
      ∑ i, (b.repr x i - round (b.repr x i)) • (i : Fin n → ℝ) := by
    have hsum : x = ∑ i, b.repr x i • (i : Fin n → ℝ) := by
      conv_lhs => rw [← b.sum_repr x]
      simp [b]
    nth_rw 1 [hsum]
    simp only [map_sum, map_zsmul, (hv _).2, sub_smul, Finset.sum_sub_distrib,
      Int.cast_smul_eq_zsmul]
  have h := sum_smul_mem_smul_of_abs_le hK.convex hK.neg_mem hK.nonempty
    (fun i ↦ (hv i).2 ▸ mem_latticePoints.1 (hv i).1) fun i ↦ by
      simpa using abs_sub_round (b.repr x i)
  rw [hx]
  rwa [hcard] at h

/-- A full symmetric body `K ⊆ ℝ ^ n` has at most `(1 + n / 2) ^ n * vol K` integer points. -/
lemma ncard_latticePoints_le :
    ((latticePoints K).ncard : ℝ) ≤ (1 + n / 2) ^ n * volume.real K := by
  have hS : ((1 + n / 2 : ℝ) • K) = K + (n / 2 : ℝ) • K := by
    rw [hK.convex.add_smul zero_le_one (by positivity), one_smul]
  have h := card_le_volume_of_forall_exists_add_mem
    (hK.isCompact.smul (1 + n / 2 : ℝ)).isClosed.measurableSet hK.finite_latticePoints.toFinset
    fun x ↦ ?_
  · rw [Measure.addHaar_smul, finrank_fin_fun, abs_of_nonneg (by positivity)] at h
    rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset] at h
    have h' := ENNReal.toReal_mono (by finiteness [hK.volume_ne_top]) h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_natCast] at h'
  · obtain ⟨z, hz⟩ := hK.exists_sub_mem_smul x
    refine ⟨z, fun v hv ↦ ?_⟩
    rw [hS, map_sub, sub_add_eq_add_sub, add_sub_assoc]
    exact Set.add_mem_add (by simpa using hv) hz

/-- For `1 ≤ c`, the dilate `c • K` has at most `(c * (1 + n / 2)) ^ n * vol K` integer points. -/
lemma ncard_latticePoints_smul_le {c : ℝ} (hc : 1 ≤ c) :
    ((latticePoints (c • K)).ncard : ℝ) ≤ (c * (1 + n / 2)) ^ n * volume.real K := by
  grw [(hK.smul hc).ncard_latticePoints_le, volume_real_smul (by linarith), mul_pow, ← mul_assoc,
    mul_comm (c ^ n)]

end IsFullSymmetricBody

/-- **van der Corput's theorem**: a symmetric convex compact set `K ⊆ ℝ ^ n` has volume at most the
number of integer points of `2 • K`. -/
lemma volume_real_le_ncard_latticePoints_two_smul {K : Set (Fin n → ℝ)} (hK : Convex ℝ K)
    (hKc : IsCompact K) (hsymm : ∀ x ∈ K, -x ∈ K) :
    volume.real K ≤ (latticePoints ((2 : ℝ) • K)).ncard := by
  have h := volume_le_encard_latticePoints_sub hKc.isClosed.measurableSet hKc.measure_lt_top.ne
  rw [sub_self_eq_two_smul hK hsymm,
    ← (finite_latticePoints (hKc.smul (2 : ℝ)).isBounded).cast_ncard_eq] at h
  exact (ENNReal.toReal_mono (by simp) h).trans_eq (by simp)

end

end ChangFreimanRuzsa
