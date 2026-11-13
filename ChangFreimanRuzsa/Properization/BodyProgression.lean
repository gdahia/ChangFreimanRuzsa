/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GAP.Basic
public import ChangFreimanRuzsa.GeometryOfNumbers.SymmetricBody
public import Mathlib.Analysis.Convex.Body
import ChangFreimanRuzsa.GAP.Symmetric
import ChangFreimanRuzsa.Properization.RelationQuotient
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import TauCeti.Algebra.Order.BigOperators.Factorial
import TauCeti.Analysis.Convex.Combination
import TauCeti.Analysis.Convex.Topology
import TauCeti.MeasureTheory.Measure.Lebesgue.Weighted.Crosspolytope
import TauCeti.NumberTheory.GeometryOfNumbers.MinkowskiSecond

/-!
# Proper progressions from symmetric bodies

Let `K ⊆ ℝ ^ r` be a full symmetric body and `ψ : (Fin r → ℤ) →+ G`, and let `1 ≤ t`. If `ψ` is
injective on the integer points of `(2 * t * r * r! ^ 2) • K`, then `ψ '' latticePoints K` lies in
a `t`-proper progression of dimension at most `r` with at most `(3 * r! ^ 2) ^ r * r! * vol K`
elements. This is Lemma 1.5 of Green's notes *Progressions and convex geometry*.

The proof takes a basis `w` of `ℤ ^ r` with `w i ∈ a i • K`, where `a i ≤ r` and
`(∏ i, a i) * vol K ≤ 2 * r!`, from the successive minima of `K` and Minkowski's second theorem.
The cross-polytope spanned by the points `(a i)⁻¹ • w i` lies in `K`, so `2 ^ r / r! ≤ (∏ i, a i) *
vol K`. Replacing `w j` by an integer point `v` of `K` gives a cross-polytope in `K` of volume
`2 ^ r / r! * |μ j| / ∏ i ≠ j, a i`, where `μ j` is the `j`-th coefficient of `v` in `w`, so
`|μ j| ≤ r! ^ 2 / a j`. The progression is the symmetric progression with steps `ψ (w i)` and
half-lengths `⌊r! ^ 2 / a i⌋`.

## Main statements

* `exists_tProperGAP_image_latticePoints_subset_of_injOn`: the progression.
-/

public section

namespace ChangFreimanRuzsa

open MeasureTheory Module Set
open scoped Pointwise

noncomputable section

variable {r : ℕ} {K : Set (Fin r → ℝ)}

/-! ## A basis from the successive minima -/

private lemma IsFullSymmetricBody.zero_mem_interior (hK : IsFullSymmetricBody K) :
    (0 : Fin r → ℝ) ∈ interior K := by
  refine hK.convex.zero_mem_interior_of_symmetric hK.neg_mem
    ((hK.convex.interior_nonempty_iff_affineSpan_eq_top).2 ?_)
  rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty _ _ _ hK.nonempty,
    vectorSpan_eq_span_vsub_set_right ℝ hK.zero_mem, eq_top_iff, ← hK.span_latticePoints]
  apply Submodule.span_mono
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨_, hv, by simp⟩

/-- The integer vectors, as the standard lattice. -/
private def latticeEquiv (r : ℕ) : (Fin r → ℤ) ≃ₗ[ℤ] standardIntegerLattice r :=
  LinearEquiv.ofBijective (LinearMap.codRestrict _ intVectorToReal.toIntLinearMap
      intVectorToReal_mem_standardIntegerLattice)
    ⟨fun _ _ h ↦ intVectorToReal_injective (congr_arg Subtype.val h), fun ⟨_, hx⟩ ↦ by
      obtain ⟨v, rfl⟩ := exists_intVectorToReal_of_mem_standardIntegerLattice hx
      exact ⟨v, rfl⟩⟩

private lemma coe_latticeEquiv (v : Fin r → ℤ) :
    (latticeEquiv r v : Fin r → ℝ) = intVectorToReal v :=
  rfl

private instance : IsZLattice ℝ (standardIntegerLattice r) := by
  unfold standardIntegerLattice
  infer_instance

private lemma covolume_standardIntegerLattice :
    ZLattice.covolume (standardIntegerLattice r) = 1 := by
  rw [standardIntegerLattice, ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ (Fin r)) volume),
    ZSpan.volume_real_fundamentalDomain, ← Pi.basisFun_det_apply, Basis.det_self, abs_one]

/-- A full symmetric body `K ⊆ ℝ ^ r` has a basis `w` of `ℤ ^ r` with `w i ∈ a i • K` for numbers
`0 < a i ≤ r` with `(∏ i, a i) * vol K ≤ 2 * r!`. The numbers are `a i = c i * λ i` for the
successive minima `λ i ≤ 1` of `K`, where `∏ i, c i = r! / 2 ^ (r - 1)`, and Minkowski's second
theorem gives `(∏ i, λ i) * vol K ≤ 2 ^ r`. -/
private lemma exists_basis_mem_smul (hK : IsFullSymmetricBody K) :
    ∃ (w : Basis (Fin r) ℤ (Fin r → ℤ)) (a : Fin r → ℝ), (∀ i, 0 < a i) ∧ (∀ i, a i ≤ r) ∧
      (∀ i, intVectorToReal (w i) ∈ a i • K) ∧ (∏ i, a i) * volume.real K ≤ 2 * r.factorial := by
  set L := standardIntegerLattice r
  set K' : ConvexBody (Fin r → ℝ) := ⟨K, hK.convex, hK.isCompact, hK.nonempty⟩
  have h0 : (0 : Fin r → ℝ) ∈ interior (K' : Set (Fin r → ℝ)) := hK.zero_mem_interior
  obtain ⟨b, hb⟩ := ZLattice.exists_basis_mem_smul_successiveMin L h0 hK.neg_mem
  have hn : finrank ℝ (Fin r → ℝ) = r := finrank_fin_fun ℝ
  set e : Fin (finrank ℝ (Fin r → ℝ)) ≃ Fin r := finCongr hn
  set c : Fin (finrank ℝ (Fin r → ℝ)) → ℝ :=
    fun i ↦ max 1 ((((i : ℕ) : ℝ) + 1) / 2) * ZLattice.successiveMin L K' i
  refine ⟨(b.map (latticeEquiv r).symm).reindex e, c ∘ e.symm, ?_, ?_, ?_, ?_⟩
  · intro i
    exact mul_pos (lt_max_of_lt_left one_pos) (ZLattice.successiveMin_pos L h0 _)
  · intro i
    have hlam : ZLattice.successiveMin L K' (e.symm i) ≤ 1 := by
      rw [ZLattice.successiveMin_le_iff_finrank L h0 zero_le_one, one_smul,
        eq_top_mono (Submodule.span_mono ?_) hK.span_latticePoints, finrank_top]
      · exact (e.symm i).isLt
      · rintro _ ⟨v, hv, rfl⟩
        exact ⟨intVectorToReal_mem_standardIntegerLattice v, hv⟩
    have hi : ((e.symm i : ℕ) : ℝ) + 1 ≤ r := by
      exact_mod_cast (by grind [(e.symm i).isLt] : (e.symm i : ℕ) + 1 ≤ r)
    exact (mul_le_of_le_one_right (by positivity) hlam).trans (max_le (by linarith) (by linarith))
  · intro i
    rw [Basis.reindex_apply, Basis.map_apply, ← coe_latticeEquiv, LinearEquiv.apply_symm_apply]
    exact hb (e.symm i)
  · have h : (∏ i, ZLattice.successiveMin L K' i) * volume.real K ≤
        2 ^ finrank ℝ (Fin r → ℝ) := by
      have := ZLattice.prod_successiveMin_mul_measureReal_le_two_pow_mul_covolume L volume
        (K := K') hK.neg_mem
      rwa [covolume_standardIntegerLattice, mul_one] at this
    rw [Function.comp_def, e.symm.prod_comp c, Finset.prod_mul_distrib,
      TauCeti.prod_max_one_add_one_div_two, mul_assoc]
    grw [h, hn]
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · simp [h0]
    · have h2 : (2 : ℝ) ^ r = 2 * 2 ^ (r - 1) := by rw [← pow_succ', Nat.sub_add_cancel hpos]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity), h2]
      exact (by ring : _ = _).le

/-! ## Cross-polytopes -/

/-- If `u i ∈ a i • K` for a symmetric convex compact `K` and `0 < a i`, then the cross-polytope
spanned by the points `(a i)⁻¹ • u i` lies in `K`, so
`2 ^ r / r! * |det u| ≤ (∏ i, a i) * vol K`. -/
private lemma two_pow_div_factorial_mul_abs_det_le (hK : Convex ℝ K) (hKc : IsCompact K)
    (h0 : 0 ∈ K) (hsymm : ∀ x ∈ K, -x ∈ K) {u : Fin r → Fin r → ℝ} {a : Fin r → ℝ}
    (ha : ∀ i, 0 < a i) (hu : ∀ i, u i ∈ a i • K) :
    2 ^ r / r.factorial * |(Matrix.of u).det| ≤ (∏ i, a i) * volume.real K := by
  have hprod : 0 < ∏ i, a i := Finset.prod_pos fun i _ ↦ ha i
  by_cases hdet : (Matrix.of u).det = 0
  · rw [hdet, abs_zero, mul_zero]
    exact mul_nonneg hprod.le measureReal_nonneg
  obtain ⟨hli, hsp⟩ := (Pi.basisFun ℝ (Fin r)).is_basis_iff_det.2
    (by rw [Pi.basisFun_det_apply]; exact Ne.isUnit hdet)
  set B := Basis.mk hli hsp.ge
  have hB : ⇑B = u := Basis.coe_mk hli hsp.ge
  have h := measure_mono (μ := volume) (hK.weighted_crosspolytope_subset h0 hsymm B ha
    (by simpa [hB] using hu))
  rw [B.addHaar_weighted_crosspolytope volume ha, ZSpan.volume_fundamentalDomain, hB,
    Fintype.card_fin, ← ENNReal.ofReal_mul (by positivity)] at h
  have h' := (ENNReal.ofReal_le_iff_le_toReal hKc.measure_lt_top.ne).1 h
  rw [← measureReal_def, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hprod] at h'
  rwa [div_mul_eq_mul_div, mul_comm (∏ i, a i)]

/-- **Cramer's rule** for the real extension of an integral basis `w`: replacing `w j` by `x`
gives determinant `± (j-th coordinate of x)`. -/
private lemma abs_det_update_basisToReal (w : Basis (Fin r) ℤ (Fin r → ℤ)) (x : Fin r → ℝ)
    (j : Fin r) :
    |(Matrix.of (Function.update (basisToReal w) j x)).det| = |(basisToReal w).repr x j| := by
  set bR := basisToReal w
  have h := congr_arg (fun f ↦ f x) ((Pi.basisFun ℝ (Fin r)).det_smul_mk_coord_eq_det_update
    bR.linearIndependent (by rw [bR.span_eq]) j)
  have hmk : Basis.mk bR.linearIndependent (by rw [bR.span_eq]) = bR :=
    Basis.eq_of_apply_eq fun i ↦ by simp
  simp only [hmk, LinearMap.smul_apply, Basis.coord_apply, smul_eq_mul,
    MultilinearMap.toLinearMap_apply, AlternatingMap.coe_multilinearMap] at h
  rw [← Pi.basisFun_det_apply, ← h, abs_mul, abs_det_basisToReal, one_mul]

/-- In a basis `w` of `ℤ ^ r` with `w i ∈ a i • K` and `(∏ i, a i) * vol K ≤ 2 * r!`, the
coefficients of an integer point of `K` satisfy `|μ j| ≤ r! ^ 2 / a j`. -/
private lemma abs_repr_le (hK : IsFullSymmetricBody K) {w : Basis (Fin r) ℤ (Fin r → ℤ)}
    {a : Fin r → ℝ} (ha : ∀ i, 0 < a i) (hw : ∀ i, intVectorToReal (w i) ∈ a i • K)
    (hprod : (∏ i, a i) * volume.real K ≤ 2 * r.factorial) {v : Fin r → ℤ}
    (hv : v ∈ latticePoints K) (j : Fin r) :
    |(w.repr v j : ℝ)| ≤ r.factorial ^ 2 / a j := by
  have hr : 1 ≤ r := Fin.pos j
  have h := two_pow_div_factorial_mul_abs_det_le hK.convex hK.isCompact hK.zero_mem hK.neg_mem
    (u := Function.update (basisToReal w) j (intVectorToReal v))
    (a := Function.update a j 1) (fun i ↦ by
      rcases eq_or_ne i j with rfl | hij
      · simp
      · simpa [hij] using ha i) (fun i ↦ by
      rcases eq_or_ne i j with rfl | hij
      · simpa using hv
      · simpa [hij, basisToReal_apply] using hw i)
  rw [abs_det_update_basisToReal, basisToReal_repr_intCast,
    Finset.prod_update_of_mem (Finset.mem_univ j), one_mul] at h
  have hsplit := Finset.mul_prod_erase Finset.univ a (Finset.mem_univ j)
  rw [Finset.sdiff_singleton_eq_erase] at h
  rw [le_div_iff₀ (ha j)]
  have h2 : (2 : ℝ) ≤ 2 ^ r := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ r := pow_le_pow_right₀ one_le_two hr
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h
  have h3 : 2 ^ r * (|(w.repr v j : ℝ)| * a j) ≤ 2 * r.factorial * r.factorial := by
    calc 2 ^ r * (|(w.repr v j : ℝ)| * a j) = 2 ^ r * |(w.repr v j : ℝ)| * a j := by ring
      _ ≤ (∏ x ∈ Finset.univ.erase j, a x) * volume.real K * r.factorial * a j := by
        gcongr
        exact (ha j).le
      _ = (∏ i, a i) * volume.real K * r.factorial := by
        rw [← hsplit]
        ring
      _ ≤ 2 * r.factorial * r.factorial := by gcongr
  nlinarith [mul_le_mul_of_nonneg_right h2
    (mul_nonneg (abs_nonneg (w.repr v j : ℝ)) (ha j).le)]

/-! ## The progression -/

variable {G : Type*} [AddCommGroup G]

/-- **A proper progression from a symmetric body.** Let `K ⊆ ℝ ^ r` be a full symmetric body,
`1 ≤ t` and `ψ : (Fin r → ℤ) →+ G` injective on the integer points of
`(2 * t * r * r! ^ 2) • K`. Then `ψ '' latticePoints K` lies in a `t`-proper progression of
dimension at most `r` with at most `(3 * r! ^ 2) ^ r * r! * vol K` elements. -/
lemma exists_tProperGAP_image_latticePoints_subset_of_injOn [DecidableEq G]
    (hK : IsFullSymmetricBody K) {t : ℕ} (ht : 1 ≤ t) {ψ : (Fin r → ℤ) →+ G}
    (hψ : InjOn ψ (latticePoints ((2 * t * r * r.factorial ^ 2 : ℝ) • K))) :
    ∃ Q : GAP G, (t • Q).Proper ∧ ψ '' latticePoints K ⊆ Q.toFinset ∧ Q.dim ≤ r ∧
      Q.toFinset.card ≤ (3 * r.factorial ^ 2) ^ r * r.factorial * volume.real K := by
  obtain ⟨w, a, ha, har, hw, hprod⟩ := exists_basis_mem_smul hK
  set M : ℝ := r.factorial ^ 2 with hMdef
  have hM : 0 < M := by positivity
  have haM (i : Fin r) : a i ≤ M := (har i).trans (by
    rw [hMdef]
    exact_mod_cast (Nat.self_le_factorial r).trans (Nat.le_self_pow two_ne_zero _))
  have hN (i : Fin r) : (⌊M / a i⌋₊ : ℝ) ≤ M / a i := Nat.floor_le (div_pos hM (ha i)).le
  refine ⟨symmetricGAP (fun i ↦ ψ (w i)) fun i ↦ ⌊M / a i⌋₊, ?_, ?_, dim_symmetricGAP_le, ?_⟩
  · rw [nsmul_symmetricGAP]
    refine proper_symmetricGAP fun n hn hn0 ↦ ?_
    choose k hk hka using hw
    have ht' : (0 : ℝ) < 4 * t * M := by positivity
    have hu : intVectorToReal (w.equivFun.symm n) ∈ (2 * t * r * r.factorial ^ 2 : ℝ) • K := by
      have hsum := sum_smul_mem_smul_of_abs_le hK.convex hK.neg_mem hK.nonempty hk
        (a := fun i ↦ n i * a i / (4 * t * M)) fun i ↦ by
          rw [abs_div, abs_mul, abs_of_pos (ha i), abs_of_pos ht', div_le_iff₀ ht']
          have hni : |(n i : ℝ)| ≤ 2 * (t * ⌊M / a i⌋₊) := by exact_mod_cast hn i
          have hai := (ha i).ne'
          calc |(n i : ℝ)| * a i ≤ 2 * (t * (M / a i)) * a i :=
                mul_le_mul_of_nonneg_right (hni.trans (by gcongr; exact hN i)) (ha i).le
            _ = 1 / 2 * (4 * t * M) := by
                field_simp
                ring
      rw [Fintype.card_fin] at hsum
      convert smul_mem_smul_set (a := 4 * t * M) hsum using 1
      · rw [smul_smul]
        congr 1
        ring
      · rw [Basis.equivFun_symm_apply, map_sum, Finset.smul_sum]
        congr with i
        rw [map_zsmul, ← hka, ← Int.cast_smul_eq_zsmul ℝ, smul_smul, smul_smul]
        field_simp
    have h0 : (0 : Fin r → ℤ) ∈ latticePoints ((2 * t * r * r.factorial ^ 2 : ℝ) • K) := by
      rw [mem_latticePoints, map_zero]
      exact zero_mem_smul_set hK.zero_mem
    have hψu : ψ (w.equivFun.symm n) = ψ 0 := by
      rw [map_zero, ← hn0, stepsHom_apply, Basis.equivFun_symm_apply, map_sum]
      simp_rw [map_zsmul]
    have := congr_arg w.equivFun (hψ hu h0 hψu)
    rw [LinearEquiv.apply_symm_apply, map_zero] at this
    exact congr_fun this
  · rintro _ ⟨v, hv, rfl⟩
    have hψv : ψ v = stepsHom (fun i ↦ ψ (w i)) (w.equivFun v) := by
      conv_lhs => rw [← w.sum_repr v]
      rw [map_sum, stepsHom_apply]
      simp_rw [map_zsmul]
      rfl
    rw [hψv]
    refine stepsHom_mem_symmetricGAP fun i ↦ ?_
    rw [Basis.equivFun_apply, Int.abs_eq_natAbs, Nat.cast_le, Nat.le_floor_iff
      (div_pos hM (ha i)).le, Nat.cast_natAbs, Int.cast_abs]
    exact abs_repr_le hK ha hw hprod hv i
  · have hpos : 0 < ∏ i, a i := Finset.prod_pos fun i _ ↦ ha i
    have hlow : 2 ^ r / r.factorial ≤ (∏ i, a i) * volume.real K := by
      have h := two_pow_div_factorial_mul_abs_det_le hK.convex hK.isCompact hK.zero_mem
        hK.neg_mem (u := basisToReal w) ha fun i ↦ by simpa [basisToReal_apply] using hw i
      rwa [← Pi.basisFun_det_apply, abs_det_basisToReal, mul_one] at h
    have hcard := Nat.cast_le (α := ℝ).2
      (card_symmetricGAP_le (x := fun i ↦ ψ (w i)) (L := fun i ↦ ⌊M / a i⌋₊))
    rw [Nat.cast_prod] at hcard
    refine hcard.trans ?_
    calc ∏ i, (((2 * ⌊M / a i⌋₊ + 1 : ℕ)) : ℝ) ≤ ∏ i, (3 * M / a i) := by
          gcongr with i
          have h1 : 1 ≤ M / a i := (one_le_div (ha i)).2 (haM i)
          push_cast
          rw [mul_div_assoc]
          linarith [hN i]
      _ = (3 * M) ^ r / ∏ i, a i := by
        rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ (3 * M) ^ r * r.factorial * volume.real K := by
        rw [div_le_iff₀ hpos, mul_assoc, mul_assoc]
        refine le_mul_of_one_le_right (by positivity) ?_
        rw [div_le_iff₀ (by positivity)] at hlow
        nlinarith [one_le_pow₀ (n := r) (one_le_two (α := ℝ))]

end

end ChangFreimanRuzsa
