/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.Container
public import ChangFreimanRuzsa.Properization.ShortRelationsAndIteration

/-!
# Chang's theorem in `ZMod q`

Let `q` be a prime and let `X ⊆ ZMod q` satisfy `|X + X| ≤ κ * |X|`. If `X` is neither too small
nor too large compared with `q`, then `X` lies in a `2`-proper generalized arithmetic progression
of bounded dimension and of size at most a constant multiple of `|X|`.

The proof composes the two stages of the argument: `exists_coarseGAP_container` puts `X` in a
progression of bounded dimension and size, and `exists_twoProperGAP_container` replaces that
progression by a `2`-proper one.

## Main definitions

* `changZModExponent κ`: the budget for the size of the progression.

## Main statements

* `exists_twoProperGAP_zmod_of_small_sumset`: Chang's theorem in `ZMod q`.
-/

public section

open Finset
open scoped Pointwise

namespace ChangFreimanRuzsa

/-- The budget of Chang's theorem in `ZMod q`. -/
@[expose] noncomputable def changZModExponent (κ : ℝ) : ℝ :=
  properizationConstant * (changContainerExponent κ + 2) ^ 4 + changContainerExponent κ

private lemma exp_mul_le_exp_add_mul {a c d x y : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) (hdc : d ≤ c)
    (hy : 0 ≤ y) (hyx : y ≤ Real.exp c * x) :
    Real.exp (a * (d + 2) ^ 4) * y ≤ Real.exp (a * (c + 2) ^ 4 + c) * x := by
  rw [Real.exp_add, mul_assoc]
  gcongr

/-- **Chang's theorem** in `ZMod q` for a prime `q`: a set `X` with `|X + X| ≤ κ * |X|`,
`exp (changContainerExponent κ) < |X|` and `exp (changZModExponent κ) * |X| ≤ q` is contained in a
`2`-proper GAP of dimension at most `changContainerExponent κ` and size at most
`exp (changZModExponent κ) * |X|`. -/
theorem exists_twoProperGAP_zmod_of_small_sumset {q : ℕ} {κ : ℝ} (X : Finset (ZMod q))
    (hq : q.Prime) (hκ : 2 ≤ κ) (hXX : (#(X + X) : ℝ) ≤ κ * #X)
    (hXlower : Real.exp (changContainerExponent κ) < #X)
    (hXupper : Real.exp (changZModExponent κ) * #X ≤ q) :
    ∃ Q : GAP (ZMod q), Q.TwoProper ∧ X ⊆ Q.carrier ∧ (∀ i, 1 < Q.length i) ∧
      (Q.dim : ℝ) ≤ changContainerExponent κ ∧
      (#Q.carrier : ℝ) ≤ Real.exp (changZModExponent κ) * #X := by
  obtain ⟨P, hXP, -, hPdim, hPcard⟩ := exists_coarseGAP_container X hq hκ hXX hXlower
  have hP : Real.exp (properizationConstant * ((P.dim : ℝ) + 2) ^ 4) * #P.carrier ≤
      Real.exp (changZModExponent κ) * #X :=
    exp_mul_le_exp_add_mul properizationConstant_pos.le (Nat.cast_nonneg _) hPdim
      (Nat.cast_nonneg _) hPcard
  obtain ⟨Q, hQ, hPQ, hlen, hQdim, hQcard⟩ := exists_twoProperGAP_container P hq (hP.trans hXupper)
  exact ⟨Q, hQ, hXP.trans hPQ, hlen, (Nat.cast_le.2 hQdim).trans hPdim, hQcard.trans hP⟩

end ChangFreimanRuzsa
