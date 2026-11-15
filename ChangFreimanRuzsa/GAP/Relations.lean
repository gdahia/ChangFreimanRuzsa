/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GAP.Basic
import Mathlib.Algebra.Order.Group.Abs

/-!
# The lattice of relations of a progression

The relations of a GAP with steps `step : Fin d → G` are the integer vectors `v` with
`∑ i, v i • step i = 0`. They form the kernel of the step homomorphism from `ℤ ^ d` to `G`.

## Main statements

* `GAP.proper_iff`: a progression is proper if and only if no nonzero relation has
  `|v i| ≤ P.bound i` for all `i`.
* `GAP.proper_nsmul_iff`: a progression is `t`-proper if and only if no nonzero relation has
  `|v i| ≤ t * P.bound i` for all `i`.
* `GAP.mem_toFinset_iff_exists_intCoeffs`: membership in a progression through integer
  coefficients.
-/

@[expose] public section

namespace ChangFreimanRuzsa

variable {G : Type*} [AddCommGroup G]

namespace GAP

/-- The lattice of relations among the steps of a GAP. -/
noncomputable def relations (P : GAP G) : AddSubgroup (Fin P.dim → ℤ) := (stepHom P).ker

/-- A progression is proper if and only if its steps admit no nonzero relation whose coefficients
are bounded by the bounds. -/
lemma proper_iff (P : GAP G) :
    P.Proper ↔ ∀ v ∈ P.relations, (∀ i, |v i| ≤ P.bound i) → v = 0 := by
  simp only [relations, AddMonoidHom.mem_ker, stepHom]
  constructor
  · intro hP v hv hle
    have heq : P.eval (fun i ↦ (v i).toNat) = P.eval (fun i ↦ (-v i).toNat) := by
      rw [eval_eq_stepsHom, eval_eq_stepsHom, add_right_inj, ← sub_eq_zero, ← map_sub, ← hv]
      congr with i
      grind [Pi.sub_apply]
    funext i
    rw [Pi.zero_apply]
    grind [congr_fun (hP (fun j ↦ by grind [abs_le, hle j]) (fun j ↦ by grind [abs_le, hle j])
      heq) i]
  · intro hrel w₁ hw₁ w₂ hw₂ hw
    rw [eval_eq_stepsHom, eval_eq_stepsHom, add_right_inj, ← sub_eq_zero, ← map_sub] at hw
    funext i
    simpa [sub_eq_zero] using
      congr_fun (hrel _ hw fun j ↦ by grind [Pi.sub_apply, abs_le, hw₁ j, hw₂ j]) i

/-- A progression is `t`-proper if and only if no nonzero relation `v` has `|v i| ≤ t * P.bound i`
for all `i`. -/
lemma proper_nsmul_iff (t : ℕ) (P : GAP G) :
    (t • P).Proper ↔ ∀ v ∈ P.relations, (∀ i, |v i| ≤ t * P.bound i) → v = 0 := by
  rw [proper_iff]
  rfl

/-- A translate of a progression is `t`-proper if and only if the progression is. -/
lemma proper_nsmul_vadd_iff (t : ℕ) (c : G) (P : GAP G) :
    (t • (c +ᵥ P)).Proper ↔ (t • P).Proper := by
  rw [proper_nsmul_iff, proper_nsmul_iff]
  rfl

/-- Membership in a progression, in terms of integer coefficients in the coefficient box. -/
lemma mem_toFinset_iff_exists_intCoeffs [DecidableEq G] (P : GAP G) {x : G} :
    x ∈ (P : Finset G) ↔ ∃ c : Fin P.dim → ℤ, (∀ i, 0 ≤ c i ∧ c i ≤ P.bound i) ∧
      x = P.origin + stepsHom P.step c := by
  rw [mem_toFinset]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨fun i ↦ (w i : ℤ), fun i ↦ by grind [hw i], P.eval_eq_stepsHom w⟩
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun i ↦ (c i).toNat, fun i ↦ by grind [hc i], ?_⟩
    rw [eval_eq_stepsHom]
    congr with i
    grind [hc i]

end GAP

end ChangFreimanRuzsa
