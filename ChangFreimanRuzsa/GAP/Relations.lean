/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GAP.Basic

/-!
# The lattice of relations of a progression

The relations of a GAP with steps `step : Fin d → G` are the integer vectors `v` with
`∑ i, v i • step i = 0`. They form the kernel of the step homomorphism from `ℤ ^ d` to `G`.

## Main statements

* `injective_gapMap_iff`: a progression is proper if and only if no nonzero relation has
  `|v i| < length i` for all `i`.
* `GAP.proper_nsmul_iff`: a progression is `t`-proper if and only if no nonzero relation has
  `|v i| ≤ t * (P.length i - 1)` for all `i`.
* `GAP.Proper.of_nsmul_of_le`: a `t`-proper progression is `s`-proper for `s ≤ t`.
* `GAP.injective_gapMap_mul_length_of_proper_two_mul_nsmul`: if `(2 * t) • P` is proper, then `P` is
  `t`-proper in the sense of Green and Tao.
* `GAP.mem_toFinset_iff_exists_intCoeffs`: membership in a progression through integer
  coefficients.
-/

@[expose] public section

namespace ChangFreimanRuzsa

section Steps

variable {G : Type*} [AddCommGroup G]

/-- The element of a GAP with prescribed coefficients, read through the step homomorphism. -/
lemma gapMap_eq_stepsHom {d : ℕ} (origin : G) (step : Fin d → G) (length : Fin d → ℕ)
    (w : (i : Fin d) → Fin (length i)) :
    gapMap origin step length w = origin + stepsHom step fun i ↦ ((w i : ℕ) : ℤ) := by
  rw [stepsHom_natCast]
  rfl

/-- A progression is proper if and only if its steps admit no nonzero relation whose coefficients
are bounded by the lengths. -/
lemma injective_gapMap_iff {d : ℕ} (origin : G) (step : Fin d → G) (length : Fin d → ℕ) :
    Function.Injective (gapMap origin step length) ↔
      ∀ v : Fin d → ℤ, stepsHom step v = 0 → (∀ i, |v i| < length i) → v = 0 := by
  constructor
  · intro hinj v hv hlt
    have heq : gapMap origin step length (fun i ↦ ⟨(v i).toNat, by grind [abs_lt.mp (hlt i)]⟩) =
        gapMap origin step length (fun i ↦ ⟨(-v i).toNat, by grind [abs_lt.mp (hlt i)]⟩) := by
      rw [gapMap_eq_stepsHom, gapMap_eq_stepsHom, add_right_inj, ← sub_eq_zero, ← map_sub, ← hv]
      congr with i
      grind [Pi.sub_apply]
    funext i
    rw [Pi.zero_apply]
    grind [congr_arg (fun w ↦ (w i : ℕ)) (hinj heq)]
  · intro hrel w₁ w₂ hw
    rw [gapMap_eq_stepsHom, gapMap_eq_stepsHom, add_right_inj, ← sub_eq_zero, ← map_sub] at hw
    ext i
    simpa [sub_eq_zero] using congr_fun (hrel _ hw fun j ↦ by grind [Pi.sub_apply, abs_lt]) i

/-- Membership in the image of `gapMap`, in terms of integer coefficients in the coefficient
box. -/
lemma mem_image_gapMap_iff_exists_intCoeffs [DecidableEq G] {d : ℕ} {origin : G}
    {step : Fin d → G} {length : Fin d → ℕ} {x : G} :
    x ∈ Finset.univ.image (gapMap origin step length) ↔
      ∃ c : Fin d → ℤ, (∀ i, 0 ≤ c i ∧ c i < length i) ∧ x = origin + stepsHom step c := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨w, -, rfl⟩
    exact ⟨fun i ↦ ((w i : ℕ) : ℤ), by simp, gapMap_eq_stepsHom _ _ _ _⟩
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun i ↦ ⟨(c i).toNat, by grind [hc i]⟩, Finset.mem_univ _, ?_⟩
    rw [gapMap_eq_stepsHom]
    congr with i
    grind [hc i]

end Steps

variable {G : Type*} [AddCommGroup G]

namespace GAP

/-- The lattice of relations among the steps of a GAP. -/
noncomputable def relations (P : GAP G) : AddSubgroup (Fin P.dim → ℤ) := (stepHom P).ker

lemma mem_relations {P : GAP G} {v : Fin P.dim → ℤ} :
    v ∈ P.relations ↔ ∑ i, v i • P.step i = 0 := Iff.rfl

/-- A progression is `t`-proper if and only if no nonzero relation `v` has
`|v i| ≤ t * (P.length i - 1)` for all `i`. -/
lemma proper_nsmul_iff (t : ℕ) (P : GAP G) :
    (t • P).Proper ↔ ∀ v ∈ P.relations, (∀ i, |v i| ≤ t * ((P.length i : ℤ) - 1)) → v = 0 := by
  have h (i : Fin P.dim) :
      ((t * (P.length i - 1) + 1 : ℕ) : ℤ) = t * ((P.length i : ℤ) - 1) + 1 := by
    grind [P.length_pos i]
  rw [proper_nsmul_iff_injective, injective_gapMap_iff]
  simp [relations, stepHom, h, Int.lt_add_one_iff]

/-- A `t`-proper progression is `s`-proper for `s ≤ t`. -/
lemma Proper.of_nsmul_of_le {s t : ℕ} {P : GAP G} (hst : s ≤ t) (h : (t • P).Proper) :
    (s • P).Proper := by
  rw [proper_nsmul_iff] at h ⊢
  intro v hv hle
  refine h v hv ?_
  intro i
  exact (hle i).trans (Int.mul_le_mul_of_nonneg_right (mod_cast hst) (by grind [P.length_pos i]))

/-- If `(2 * t) • P` is proper, then `P` is `t`-proper in the sense of Green and Tao: the points
`x + ∑ i, w i • P.step i` with `w i < t * P.length i` are distinct. Indeed
`t * P.length i - 1 ≤ 2 * t * (P.length i - 1)`, as `2 ≤ P.length i`. -/
lemma injective_gapMap_mul_length_of_proper_two_mul_nsmul {t : ℕ} {P : GAP G} (x : G)
    (h : ((2 * t) • P).Proper) :
    Function.Injective (gapMap x P.step fun i ↦ t * P.length i) := by
  rw [injective_gapMap_iff]
  intro v hv hlt
  refine (proper_nsmul_iff _ _).1 h v hv ?_
  intro i
  have hlt' : |v i| < t * (P.length i : ℤ) := mod_cast hlt i
  have hmul := Int.mul_le_mul_of_nonneg_left
    (by grind [P.one_lt_length i] : (P.length i : ℤ) ≤ 2 * ((P.length i : ℤ) - 1))
    (Int.natCast_nonneg t)
  push_cast
  grind

/-- Membership in a progression, in terms of integer coefficients in the coefficient box. -/
lemma mem_toFinset_iff_exists_intCoeffs [DecidableEq G] (P : GAP G) {x : G} :
    x ∈ P.toFinset ↔ ∃ c : Fin P.dim → ℤ, (∀ i, 0 ≤ c i ∧ c i < P.length i) ∧
      x = P.origin + stepsHom P.step c := by
  rw [P.toFinset_eq]
  exact mem_image_gapMap_iff_exists_intCoeffs

end GAP

end ChangFreimanRuzsa
