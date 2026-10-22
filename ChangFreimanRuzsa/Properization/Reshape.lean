/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GapToolkit
public import ChangFreimanRuzsa.GeometryOfNumbers
import ChangFreimanRuzsa.Properization.Relations

/-! # Enlarging the lengths of a progression

This file bounds the size of the progression obtained by enlarging all lengths by the same factor.

## Main definitions

* `GAP.scaleLengths`: the GAP whose lengths are those of a given one multiplied by `k`.
* `GAP.boundedStepImage`: the image under the step homomorphism of the `m`-dilate of the symmetric
  coefficient box.

## Main statements

* `GAP.card_scaleLengths_le`: multiplying the lengths of a progression `P` by `k` gives at most
  `k ^ P.dim * #P.carrier` elements.
* `GAP.card_boundedStepImage_le`: the image of the `m`-dilate of the symmetric coefficient box has
  at most `(2 * m + 1) ^ P.dim * #P.carrier` elements.
-/

@[expose] public section

namespace ChangFreimanRuzsa

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

namespace GAP

/-- Multiply every length of a progression by the same integer. -/
noncomputable def scaleLengths (P : GAP G) (k : ℕ) : GAP G :=
  ofSteps P.origin P.step fun i ↦ k * P.length i

lemma carrier_scaleLengths (P : GAP G) {k : ℕ} (hk : 0 < k) :
    (P.scaleLengths k).carrier = Finset.univ.image (gapMap P.origin P.step (k * P.length ·)) :=
  carrier_ofSteps fun i ↦ Nat.mul_pos hk (P.length_pos i)

/-- Multiplying all lengths of a progression `P` by `k` gives a progression covered by
`k ^ P.dim` translates of `P`. -/
lemma card_scaleLengths_le (P : GAP G) {k : ℕ} (hk : 0 < k) :
    (P.scaleLengths k).carrier.card ≤ k ^ P.dim * P.carrier.card := by
  have hsub : (P.scaleLengths k).carrier ⊆ (Finset.univ ×ˢ P.carrier).image
      fun ((b : Fin P.dim → Fin k), x) ↦ ∑ i, (b i * P.length i) • P.step i + x := by
    intro x hx
    rw [carrier_scaleLengths P hk] at hx
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨(fun i ↦ ⟨w i / P.length i,
      Nat.div_lt_of_lt_mul ((w i).isLt.trans_eq (mul_comm _ _))⟩,
      gapMap P.origin P.step P.length fun i ↦ ⟨w i % P.length i, Nat.mod_lt _ (P.length_pos i)⟩),
      by simp [P.carrier_eq], ?_⟩
    simp [gapMap, add_left_comm _ P.origin, ← Finset.sum_add_distrib, ← add_nsmul,
      Nat.div_add_mod']
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp

/-- The step-homomorphism image of the box dilated by `m`. -/
noncomputable def boundedStepImage (P : GAP G) (m : ℕ) : Finset G :=
  (intBox fun i ↦ m * (P.length i - 1)).image (stepHom P)

/-- The image of the `m`-dilate of the symmetric coefficient box of a progression `P` has at most
`(2 * m + 1) ^ P.dim * #P.carrier` elements: its translate by
`P.origin + ∑ i, (m * (P.length i - 1)) • P.step i` lies in the progression with lengths
`(2 * m + 1) * P.length i`. -/
lemma card_boundedStepImage_le (P : GAP G) (m : ℕ) :
    (P.boundedStepImage m).card ≤ (2 * m + 1) ^ P.dim * P.carrier.card := by
  refine (Finset.card_le_card_of_injOn (P.origin + stepHom P (fun i ↦ m * (P.length i - 1 : ℤ)) + ·)
    ?_ (add_right_injective _).injOn).trans (P.card_scaleLengths_le (by grind))
  intro z hz
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
  rw [mem_intBox] at hv
  rw [Finset.mem_coe, carrier_scaleLengths P (by grind), mem_image_gapMap_iff_exists_intCoeffs]
  refine ⟨fun i ↦ m * (P.length i - 1 : ℤ) + v i, ?_, ?_⟩
  · intro i
    obtain ⟨h₁, h₂⟩ := abs_le.mp (hv i)
    push_cast [Nat.cast_sub (P.length_pos i)] at h₁ h₂ ⊢
    constructor <;> grind [P.length_pos i]
  · beta_reduce
    rw [add_assoc, ← map_add]
    rfl

end GAP

end ChangFreimanRuzsa
