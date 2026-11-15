/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.ConvexProgression.Basic
import ChangFreimanRuzsa.Properization.RelationQuotient

/-!
# Iterated quotients of a convex progression

Let `P` be a convex progression of dimension `d` in an abelian group in which the multiples `n • a`
with `n < N` of every nonzero `a` are distinct, let its body `K ⊆ ℝ ^ d` be a full symmetric body,
and let `1 ≤ s`. Write `F d = (s * (d + 2) ^ 2) ^ d`. If `F d * vol K < N`, then repeating
`exists_quotient_of_not_injOn` gives an `s`-proper convex progression `Q ⊇ P` of dimension `m ≤ d`
whose body `K' ⊆ ℝ ^ m` is a full symmetric body with `vol K' ≤ F d * vol K`. Each step lowers the
dimension and multiplies the volume by at most `s * d ^ 2`.

## Main statements

* `ConvexProgression.exists_tProper_superset`: the iterated quotient.
-/

public section

namespace ChangFreimanRuzsa

open MeasureTheory Set
open scoped Pointwise

variable {G : Type*} [AddCommGroup G] {N : ℕ} {s : ℝ}

/-- The factor of one quotient step fits into the bound for the dimension above:
`(s * (m + 2) ^ 2) ^ m * (s * (m + 1) ^ 2) ≤ (s * (m + 3) ^ 2) ^ (m + 1)`. -/
private lemma pow_mul_le_pow_succ (hs : 0 ≤ s) (m : ℕ) :
    (s * ((m : ℝ) + 2) ^ 2) ^ m * (s * ((m : ℝ) + 1) ^ 2) ≤
      (s * (((m + 1 : ℕ) : ℝ) + 2) ^ 2) ^ (m + 1) := by
  calc (s * ((m : ℝ) + 2) ^ 2) ^ m * (s * ((m : ℝ) + 1) ^ 2)
      ≤ (s * ((m : ℝ) + 3) ^ 2) ^ m * (s * ((m : ℝ) + 3) ^ 2) := by gcongr <;> linarith
    _ = (s * (((m + 1 : ℕ) : ℝ) + 2) ^ 2) ^ (m + 1) := by
      push_cast
      ring

/-- If `1 ≤ s`, a full symmetric body `K ⊆ ℝ ^ d` has at most `(s * (d + 2) ^ 2) ^ d * vol K`
integer points in `(2 * s) • K`. -/
private lemma ncard_latticePoints_two_mul_smul_le {d : ℕ} {K : Set (Fin d → ℝ)}
    (hK : IsFullSymmetricBody K) (hs : 1 ≤ s) :
    ((latticePoints ((2 * s) • K)).ncard : ℝ) ≤ (s * (d + 2) ^ 2) ^ d * volume.real K := by
  grw [hK.ncard_latticePoints_smul_le (by linarith),
    (by ring : 2 * s * (1 + (d : ℝ) / 2) = s * (d + 2))]
  gcongr
  nlinarith

/-- **Iterated quotients.** Let `P` be a convex progression of dimension `d` whose body is a full
symmetric body, and let `1 ≤ s`. If the multiples `n • a` with `n < N` of every nonzero `a` are
distinct and `(s * (d + 2) ^ 2) ^ d * vol P.body < N`, then `P` lies in an `s`-proper convex
progression `Q` of dimension at most `d` whose body is a full symmetric body of volume at most
`(s * (d + 2) ^ 2) ^ d * vol P.body`. -/
lemma ConvexProgression.exists_tProper_superset
    (hG : ∀ a : G, a ≠ 0 → InjOn (fun n : ℕ ↦ n • a) (Iio N)) (hs : 1 ≤ s)
    (P : ConvexProgression G) (hP : IsFullSymmetricBody P.body)
    (hN : (s * (P.dim + 2) ^ 2) ^ P.dim * volume.real P.body < N) :
    ∃ Q : ConvexProgression G, Q.dim ≤ P.dim ∧ IsFullSymmetricBody Q.body ∧ Q.TProper s ∧
      P.toSet ⊆ Q.toSet ∧
        volume.real Q.body ≤ (s * (P.dim + 2) ^ 2) ^ P.dim * volume.real P.body := by
  have hF (d : ℕ) : 1 ≤ (s * ((d : ℝ) + 2) ^ 2) ^ d := one_le_pow₀
    (one_le_mul_of_one_le_of_one_le hs (one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) d])))
  obtain ⟨d, x₀, φ, K⟩ := P
  dsimp only at hP hN ⊢
  induction d with
  | zero =>
    exact ⟨⟨0, x₀, φ, K⟩, le_rfl, hP, fun _ _ _ _ _ ↦ Subsingleton.elim _ _, subset_rfl, by simp⟩
  | succ m ih =>
    by_cases hφ : InjOn φ (latticePoints (s • K))
    · exact ⟨⟨m + 1, x₀, φ, K⟩, le_rfl, hP, hφ, subset_rfl,
        le_mul_of_one_le_left measureReal_nonneg (hF _)⟩
    obtain ⟨K₁, φ₁, hK₁, hφK₁, hvol⟩ := exists_quotient_of_not_injOn hG hP (by linarith)
      (by exact_mod_cast (ncard_latticePoints_two_mul_smul_le hP hs).trans_lt hN) hφ
    have hstep : (s * ((m : ℝ) + 2) ^ 2) ^ m * volume.real K₁ ≤
        (s * (((m + 1 : ℕ) : ℝ) + 2) ^ 2) ^ (m + 1) * volume.real K := by
      grw [hvol, ← pow_mul_le_pow_succ (by linarith) m]
      exact (mul_assoc _ _ _).symm.le
    obtain ⟨Q, hQ, hQK, hQs, hPQ, hvol'⟩ := ih φ₁ K₁ hK₁ (hstep.trans_lt hN)
    exact ⟨Q, hQ.trans m.le_succ, hQK, hQs, (vadd_set_mono hφK₁).trans hPQ, hvol'.trans hstep⟩

end ChangFreimanRuzsa
