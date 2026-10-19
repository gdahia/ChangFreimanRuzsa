/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GapToolkit
public import ChangFreimanRuzsa.GeometryOfNumbers
import ChangFreimanRuzsa.Properization.Relations

/-! # Replacing the steps and lengths of a progression

This file builds progressions from prescribed data and bounds the size of the progression obtained
by enlarging all lengths by the same factor.

## Main definitions

* `GAP.ofData`: the GAP with prescribed dimension, origin, steps and lengths.
* `GAP.reshape`: a GAP with the dimension and origin of a given one and new steps and lengths.
* `GAP.scaleLengths`: the GAP whose lengths are those of a given one multiplied by $k$.
* `GAP.boundedStepImage`: the image under the step homomorphism of the $m$-dilate of the symmetric
  coefficient box.

## Main statements

* `GAP.card_scaleLengths_le`: multiplying the lengths of a progression $P$ of dimension $d$ by $k$
  gives at most $k^d |P|$ elements.
* `GAP.card_boundedStepImage_le`: the image of the $m$-dilate of the symmetric coefficient box has
  at most $(2m + 1)^d |P|$ elements.
-/

@[expose] public section

namespace ChangFreimanRuzsa

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

namespace GAP

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

lemma mem_ofData {d : ℕ} (origin : G) (step : Fin d → G) {length : Fin d → ℕ}
    (hlength : ∀ i, 0 < length i) (k : (i : Fin d) → Fin (length i)) :
    gapMap origin step length k ∈ (ofData d origin step length hlength).carrier :=
  Finset.mem_image_of_mem _ (Finset.mem_univ k)

/-- Replace the steps and lengths of a GAP, keeping its dimension and origin. -/
def reshape (P : GAP G) (step : Fin P.dim → G) (length : Fin P.dim → ℕ)
    (hlength : ∀ i, 0 < length i) : GAP G :=
  ofData P.dim P.origin step length hlength

/-- Enlarging the lengths of a progression enlarges its carrier. -/
lemma carrier_subset_reshape (P : GAP G) {length : Fin P.dim → ℕ} (hlength : ∀ i, 0 < length i)
    (hle : ∀ i, P.length i ≤ length i) :
    P.carrier ⊆ (P.reshape P.step length hlength).carrier := by
  intro x hx
  rw [P.carrier_eq, Finset.mem_image] at hx
  obtain ⟨w, -, rfl⟩ := hx
  exact mem_ofData _ _ _ fun i ↦ ⟨w i, (w i).isLt.trans_le (hle i)⟩

/-- Multiply every length of a progression by the same positive integer. -/
def scaleLengths (P : GAP G) (k : ℕ) (hk : 0 < k) : GAP G :=
  P.reshape P.step (fun i ↦ k * P.length i) fun i ↦ Nat.mul_pos hk (P.length_pos i)

@[simp] lemma scaleLengths_length (P : GAP G) (k : ℕ) (hk : 0 < k) :
    (P.scaleLengths k hk).length = fun i ↦ k * P.length i := rfl

/-- Multiplying all lengths of a progression $P$ of dimension $d$ by $k$ gives a progression covered
by $k^d$ translates of $P$. -/
lemma card_scaleLengths_le (P : GAP G) {k : ℕ} (hk : 0 < k) :
    (P.scaleLengths k hk).carrier.card ≤ k ^ P.dim * P.carrier.card := by
  have hsub : (P.scaleLengths k hk).carrier ⊆ (Finset.univ ×ˢ P.carrier).image
      fun ((b : Fin P.dim → Fin k), x) ↦ ∑ i, (b i * P.length i) • P.step i + x := by
    intro x hx
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
def boundedStepImage (P : GAP G) (m : ℕ) : Finset G :=
  (intBox fun i ↦ m * (P.length i - 1)).image (stepHom P)

/-- The image of the $m$-dilate of the symmetric coefficient box of a progression $P$ of dimension
$d$ has at most $(2m + 1)^d |P|$ elements: its translate by
$a + \sum_i m (L_i - 1) s_i$ lies in the progression with lengths $(2m + 1) L_i$. -/
lemma card_boundedStepImage_le (P : GAP G) (m : ℕ) :
    (P.boundedStepImage m).card ≤ (2 * m + 1) ^ P.dim * P.carrier.card := by
  refine (Finset.card_le_card_of_injOn (P.origin + stepHom P (fun i ↦ m * (P.length i - 1 : ℤ)) + ·)
    ?_ (add_right_injective _).injOn).trans (P.card_scaleLengths_le (by grind))
  intro z hz
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
  rw [mem_intBox] at hv
  rw [Finset.mem_coe, mem_carrier_iff_exists_intCoeffs]
  refine ⟨fun i ↦ m * (P.length i - 1 : ℤ) + v i, ?_, ?_⟩
  · intro i
    obtain ⟨h₁, h₂⟩ := abs_le.mp (hv i)
    push_cast [scaleLengths_length, Nat.cast_sub (P.length_pos i)] at h₁ h₂ ⊢
    constructor <;> grind [P.length_pos i]
  · beta_reduce
    rw [add_assoc, ← map_add]
    rfl

end GAP

end ChangFreimanRuzsa
