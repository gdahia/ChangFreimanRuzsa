/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GeometryOfNumbers.SymmetricBody
import ChangFreimanRuzsa.Properization.RelationQuotient

/-!
# Iterated quotients of a symmetric body

Let `K ⊆ ℝ ^ d` be a full symmetric body and `φ : (Fin d → ℤ) →+ G` a homomorphism into an abelian
group in which the multiples `n • a` with `n < N` of every nonzero `a` are distinct, and let
`1 ≤ s`. Write `F d = (s * (d + 2) ^ 2) ^ d`. If `F d * vol K < N`, then repeating
`exists_quotient_of_not_injOn` gives a full symmetric body `K' ⊆ ℝ ^ m` with `m ≤ d` and
`vol K' ≤ F d * vol K`, and a homomorphism `ψ : (Fin m → ℤ) →+ G`, injective on the integer points
of `s • K'`, with `φ '' latticePoints K ⊆ ψ '' latticePoints K'`. Each step lowers the dimension and
multiplies the volume by at most `s * d ^ 2`.

## Main statements

* `exists_injOn_latticePoints_smul`: the iterated quotient.
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

/-- **Iterated quotients.** Let `K ⊆ ℝ ^ d` be a full symmetric body, `1 ≤ s`, and
`φ : (Fin d → ℤ) →+ G`. If the multiples `n • a` with `n < N` of every nonzero `a` are distinct and
`(s * (d + 2) ^ 2) ^ d * vol K < N`, then there are a full symmetric body `K' ⊆ ℝ ^ m` with `m ≤ d`
and `vol K' ≤ (s * (d + 2) ^ 2) ^ d * vol K`, and `ψ : (Fin m → ℤ) →+ G`, injective on the integer
points of `s • K'`, with `φ '' latticePoints K ⊆ ψ '' latticePoints K'`. -/
lemma exists_injOn_latticePoints_smul (hG : ∀ a : G, a ≠ 0 → InjOn (fun n : ℕ ↦ n • a) (Iio N))
    (hs : 1 ≤ s) {d : ℕ} {K : Set (Fin d → ℝ)} (hK : IsFullSymmetricBody K)
    (φ : (Fin d → ℤ) →+ G) (hN : (s * (d + 2) ^ 2) ^ d * volume.real K < N) :
    ∃ (m : ℕ) (K' : Set (Fin m → ℝ)) (ψ : (Fin m → ℤ) →+ G), m ≤ d ∧ IsFullSymmetricBody K' ∧
      InjOn ψ (latticePoints (s • K')) ∧ φ '' latticePoints K ⊆ ψ '' latticePoints K' ∧
      volume.real K' ≤ (s * (d + 2) ^ 2) ^ d * volume.real K := by
  have hF (d : ℕ) : 1 ≤ (s * ((d : ℝ) + 2) ^ 2) ^ d := one_le_pow₀
    (one_le_mul_of_one_le_of_one_le hs (one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) d])))
  induction d with
  | zero =>
    exact ⟨0, K, φ, le_rfl, hK, fun _ _ _ _ _ ↦ Subsingleton.elim _ _, subset_rfl, by simp⟩
  | succ m ih =>
    by_cases hφ : InjOn φ (latticePoints (s • K))
    · exact ⟨m + 1, K, φ, le_rfl, hK, hφ, subset_rfl,
        le_mul_of_one_le_left measureReal_nonneg (hF _)⟩
    obtain ⟨K₁, φ₁, hK₁, hφK₁, hvol⟩ := exists_quotient_of_not_injOn hG hK (by linarith)
      (by exact_mod_cast (ncard_latticePoints_two_mul_smul_le hK hs).trans_lt hN) hφ
    have hstep : (s * ((m : ℝ) + 2) ^ 2) ^ m * volume.real K₁ ≤
        (s * (((m + 1 : ℕ) : ℝ) + 2) ^ 2) ^ (m + 1) * volume.real K := by
      grw [hvol, ← pow_mul_le_pow_succ (by linarith) m]
      exact (mul_assoc _ _ _).symm.le
    obtain ⟨m', K', ψ, hm', hK', hψ, hφψ, hvol'⟩ := ih hK₁ φ₁ (hstep.trans_lt hN)
    exact ⟨m', K', ψ, hm'.trans m.le_succ, hK', hψ, hφK₁.trans hφψ, hvol'.trans hstep⟩

end ChangFreimanRuzsa
