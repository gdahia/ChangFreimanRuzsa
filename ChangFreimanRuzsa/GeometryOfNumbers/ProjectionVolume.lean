/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import ChangFreimanRuzsa.GeometryOfNumbers.SymmetricBody

/-!
# The volume of a projection of a symmetric convex body

Let `K ⊆ ℝ ^ (m + 1)` be a symmetric convex compact set containing the point `h • e i` of the
`i`-th coordinate axis, where `0 < h`. Dropping the `i`-th coordinate projects `K` onto a set of
volume at most `(m + 1) ^ 2 / (2 * h) * vol K`.

Write `π` for the projection and `c = 1 - 1 / (m + 1)`. For `p ∈ K` and `|u| ≤ h / (m + 1)`, the
point `c • p + u • e i` is a convex combination of `p` and a point of the segment from `-h • e i` to
`h • e i`, so it lies in `K`. Hence the fiber of `K` over each point of `c • π K` contains a segment
of length `2 * h / (m + 1)`, and Fubini's theorem gives
`2 * h / (m + 1) * vol (c • π K) ≤ vol K`. Finally `vol (c • π K) = c ^ m * vol (π K)` and
`1 / (m + 1) ≤ c ^ m` by Bernoulli's inequality.

This is the volume estimate of Lemma 2.2 of Green's notes *Progressions and convex geometry*, with
the factor `m + 1` replaced by `(m + 1) ^ 2`.

## Main statements

* `volume_image_removeNth_le`: the projection bound.
-/

public section

namespace ChangFreimanRuzsa

open MeasureTheory Set
open scoped Pointwise

variable {m : ℕ} {K : Set (Fin (m + 1) → ℝ)}

/-- If `p ∈ K` and `|u| ≤ h / (m + 1)`, then `c • p + u • e i ∈ K` for `c = 1 - 1 / (m + 1)`. -/
private lemma smul_add_single_mem (hK : Convex ℝ K) (hsymm : ∀ x ∈ K, -x ∈ K) {i : Fin (m + 1)}
    {h : ℝ} (hh : 0 < h) (hi : Pi.single i h ∈ K) {p : Fin (m + 1) → ℝ} (hp : p ∈ K) {u : ℝ}
    (hu : |u| ≤ h / (m + 1)) :
    (1 - 1 / (m + 1 : ℝ)) • p + Pi.single i u ∈ K := by
  have hm : (0 : ℝ) < m + 1 := by positivity
  have hq : Pi.single i ((m + 1) * u) ∈ K := by
    convert smul_mem_of_abs_le_one hK hsymm hi (t := (m + 1) * u / h) ?_ using 1
    · rw [← Pi.single_smul, smul_eq_mul]
      field_simp
    · rw [abs_div, abs_mul, abs_of_pos hm, abs_of_pos hh, div_le_one hh]
      rwa [le_div_iff₀' hm] at hu
  convert hK hp hq (a := 1 - 1 / (m + 1)) (b := 1 / (m + 1))
    (sub_nonneg.2 ((div_le_one hm).2 (by linarith))) (by positivity) (by ring) using 2
  rw [← Pi.single_smul, smul_eq_mul]
  field_simp

/-- **Volume of a projection.** Let `K ⊆ ℝ ^ (m + 1)` be symmetric, convex and compact, and let
`h • e i ∈ K` with `0 < h`. Dropping the `i`-th coordinate maps `K` onto a set of volume at most
`(m + 1) ^ 2 / (2 * h) * vol K`. -/
theorem volume_image_removeNth_le (hK : Convex ℝ K) (hKc : IsCompact K)
    (hsymm : ∀ x ∈ K, -x ∈ K) (i : Fin (m + 1)) {h : ℝ} (hh : 0 < h) (hi : Pi.single i h ∈ K) :
    volume (i.removeNth '' K) ≤ ENNReal.ofReal ((m + 1) ^ 2 / (2 * h)) * volume K := by
  have hm : (0 : ℝ) < m + 1 := by positivity
  set c : ℝ := 1 - 1 / (m + 1)
  have hc : 0 ≤ c := sub_nonneg.2 ((div_le_one hm).2 (by linarith))
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) i
  have hπ : Continuous (i.removeNth : (Fin (m + 1) → ℝ) → Fin m → ℝ) :=
    continuous_pi fun _ ↦ continuous_apply _
  set A := c • (i.removeNth '' K)
  have hA : MeasurableSet A := ((hKc.image hπ).smul c).isClosed.measurableSet
  have hKm : MeasurableSet (e.symm ⁻¹' K) := e.symm.measurable hKc.isClosed.measurableSet
  have hfib (w : Fin m → ℝ) : A.indicator (fun _ ↦ ENNReal.ofReal (2 * h / (m + 1))) w ≤
      volume ((fun t ↦ (t, w)) ⁻¹' (e.symm ⁻¹' K)) := by
    by_cases hw : w ∈ A
    · rw [indicator_of_mem hw]
      obtain ⟨_, ⟨p, hp, rfl⟩, rfl⟩ := hw
      refine le_trans (le_of_eq ?_) (measure_mono (s := Icc (c * p i - h / (m + 1))
        (c * p i + h / (m + 1))) fun t ht ↦ ?_)
      · rw [Real.volume_Icc]
        congr 1
        ring
      have hu : |t - c * p i| ≤ h / (m + 1) := abs_sub_le_iff.2 ⟨by linarith [ht.2],
        by linarith [ht.1]⟩
      rw [mem_preimage, mem_preimage]
      convert smul_add_single_mem hK hsymm hh hi hp hu using 1
      ext k
      induction k using i.succAboveCases with
      | x => simp [e, c]
      | p l => simp [e, c, Fin.removeNth, Fin.succAbove_ne]
    · simp [hw]
  have hK' : ENNReal.ofReal (2 * h / (m + 1)) * volume A ≤ volume K := by
    rw [← lintegral_indicator_const hA,
      ← (volume_preserving_piFinSuccAbove _ i).symm.measure_preimage_equiv K,
      Measure.volume_eq_prod, Measure.prod_apply_symm hKm]
    exact lintegral_mono hfib
  have hcm : 1 / (m + 1 : ℝ) ≤ c ^ m := by
    have := one_add_mul_le_pow (a := -(1 / (m + 1 : ℝ))) (by
      linarith [(div_le_one hm).2 (by linarith : (1 : ℝ) ≤ m + 1)]) m
    rw [← sub_eq_add_neg] at this
    convert this using 1
    field_simp
    ring
  rw [Measure.addHaar_smul, Module.finrank_fin_fun, abs_of_nonneg (pow_nonneg hc m)] at hK'
  calc volume (i.removeNth '' K)
    _ = ENNReal.ofReal ((m + 1) ^ 2 / (2 * h)) *
          (ENNReal.ofReal (2 * h / (m + 1) * (1 / (m + 1))) * volume (i.removeNth '' K)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        convert (one_mul _).symm
        rw [ENNReal.ofReal_eq_one]
        field_simp
    _ ≤ ENNReal.ofReal ((m + 1) ^ 2 / (2 * h)) * volume K := by
        gcongr
        refine le_trans ?_ hK'
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        gcongr

end ChangFreimanRuzsa
