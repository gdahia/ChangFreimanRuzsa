/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GeometryOfNumbers.SymmetricBody

/-!
# Real boxes

The real box `realBox L` of half-widths `L : Fin d → ℕ` is the set of `x : Fin d → ℝ` with
`|x i| ≤ L i` for all `i`. When every `L i` is positive it is a full symmetric body, of volume
`∏ i, 2 * L i`.

## Main definitions

* `realBox L`: the real box of half-widths `L`.

## Main statements

* `isFullSymmetricBody_realBox`: the box is a full symmetric body when every `L i` is positive.
* `volume_real_realBox`: its volume is `∏ i, 2 * L i`.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-- The real box `{x : Fin d → ℝ | ∀ i, |x i| ≤ L i}` of half-widths `L`. -/
def realBox (L : Fin d → ℕ) : Set (Fin d → ℝ) :=
  univ.pi fun i ↦ Icc (-(L i : ℝ)) (L i)

lemma mem_realBox {L : Fin d → ℕ} {x : Fin d → ℝ} : x ∈ realBox L ↔ ∀ i, |x i| ≤ L i := by
  simp [realBox, abs_le, Pi.le_def, forall_and]

/-- A real box with positive half-widths is a full symmetric body: its integer points contain the
standard basis. -/
lemma isFullSymmetricBody_realBox {L : Fin d → ℕ} (hL : ∀ i, 0 < L i) :
    IsFullSymmetricBody (realBox L) where
  convex := convex_pi fun _ _ ↦ convex_Icc _ _
  isCompact := isCompact_univ_pi fun _ ↦ isCompact_Icc
  neg_mem x hx := by simpa [mem_realBox] using hx
  nonempty := ⟨0, by simp [mem_realBox]⟩
  span_latticePoints := by
    refine eq_top_mono (Submodule.span_mono ?_) (Pi.basisFun ℝ (Fin d)).span_eq
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_, ?_⟩
    · rw [mem_latticePoints, mem_realBox]
      intro j
      rcases eq_or_ne j i with rfl | hji
      · simpa using Nat.one_le_iff_ne_zero.2 (hL j).ne'
      · simp [hji]
    · ext j
      simp [Pi.single_apply]

lemma volume_real_realBox (L : Fin d → ℕ) : volume.real (realBox L) = ∏ i, 2 * (L i : ℝ) := by
  rw [measureReal_def, realBox, volume_pi_pi, ENNReal.toReal_prod]
  congr with i
  rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [Nat.cast_nonneg (α := ℝ) (L i)])]
  ring

end

end ChangFreimanRuzsa
