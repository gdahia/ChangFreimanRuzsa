/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.Covering.Container
public import ChangFreimanRuzsa.Properization.ProperProgression

/-!
# Chang's theorem in `ZMod q`

Let `q` be a prime, let `2 ≤ t` and let `X : Finset (ZMod q)` satisfy `#(X + X) ≤ κ * #X`. Write
`F` for `freimanDimExponent κ`, `T` for `tProperExponent t (freimanDim X)` and `d` for
`bohrGAPDim κ`. If `256 * d ≤ #X` and `exp (F + T) * #X ≤ q`, then `X` lies in a `t`-proper
generalized arithmetic progression of dimension at most `freimanDim X` and with at most
`exp (F + T) * #X` points.

The proof has two stages. `exists_gap_zmod_subset_dim_le_size_le` puts `X` in a progression of
dimension at most `c = containerExponent κ` and of size at most `exp c * #X`, and
`exists_tProperGAP_subset_dim_le_freimanDim_card_le_exp` replaces that progression by a `t`-proper
one of dimension at most `freimanDim X`. The second stage holds in every abelian group in which the
multiples `n • a` with `n < q` of every nonzero `a` are distinct.

## Main definitions

* `freimanDimExponent κ`: the part of the exponent in the size bound that does not depend on `t`.

## Main statements

* `exists_tProperGAP_zmod_dim_le_freimanDim`: Chang's theorem in `ZMod q`.
-/

public section

open Finset SumOfSetsInSeveralDimensions
open scoped Pointwise

namespace ChangFreimanRuzsa

/-- The exponent `c + c * log (8 * (c + 2) ^ 3) + 1` in the size bound of Chang's theorem in
`ZMod q`, where `c` is `containerExponent κ`. -/
@[expose] noncomputable def freimanDimExponent (κ : ℝ) : ℝ :=
  containerExponent κ + containerExponent κ * Real.log (8 * (containerExponent κ + 2) ^ 3) + 1

/-- Multiples of a nonzero element of a prime cyclic group are distinct below the modulus. -/
private lemma injOn_nsmul_of_prime {q : ℕ} (hq : q.Prime) {a : ZMod q} (ha : a ≠ 0) :
    Set.InjOn (fun n : ℕ ↦ n • a) (Set.Iio q) := by
  have : Fact q.Prime := ⟨hq⟩
  intro m hm n hn h
  simp only [nsmul_eq_mul] at h
  rw [← ZMod.val_cast_of_lt hm, ← ZMod.val_cast_of_lt hn, mul_right_cancel₀ ha h]

/-- **Chang's theorem** in `ZMod q` for a prime `q`, with the dimension bounded by the Freiman
dimension. Let `2 ≤ t`, write `F` for `freimanDimExponent κ`, `T` for
`tProperExponent t (freimanDim X)` and `d` for `bohrGAPDim κ`. A set `X` with
`#(X + X) ≤ κ * #X`, `256 * d ≤ #X` and `exp (F + T) * #X ≤ q` is contained in a `t`-proper
generalized arithmetic progression of dimension at most `freimanDim X` and with at most
`exp (F + T) * #X` points. -/
theorem exists_tProperGAP_zmod_dim_le_freimanDim {q t : ℕ} {κ : ℝ} (X : Finset (ZMod q))
    (hq : q.Prime) (ht : 2 ≤ t) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X)
    (hXlower : 256 * (bohrGAPDim κ : ℝ) ≤ #X)
    (hXupper : Real.exp (freimanDimExponent κ + tProperExponent t (freimanDim X)) * #X ≤ q) :
    ∃ Q : GAP (ZMod q), (t • Q).Proper ∧ X ⊆ Q.toFinset ∧ Q.dim ≤ freimanDim X ∧
      #Q.toFinset ≤ Real.exp (freimanDimExponent κ + tProperExponent t (freimanDim X)) * #X := by
  obtain ⟨P, hXP, hPdim, hPsize⟩ := exists_gap_zmod_subset_dim_le_size_le X hq hκ hXX hXlower
  have hP : Real.exp (containerExponent κ * Real.log (8 * (containerExponent κ + 2) ^ 3) +
      tProperExponent t (freimanDim X) + 1) * P.size ≤
        Real.exp (freimanDimExponent κ + tProperExponent t (freimanDim X)) * #X := by
    grw [hPsize, ← mul_assoc, ← Real.exp_add, freimanDimExponent]
    apply le_of_eq
    ring_nf
  obtain ⟨Q, hQ, hXQ, hQdim, hQcard⟩ := exists_tProperGAP_subset_dim_le_freimanDim_card_le_exp
    (by grind) (fun _ ↦ injOn_nsmul_of_prime hq) (nonempty_of_mul_bohrGAPDim_le hXlower) hXP
    hPdim (hP.trans hXupper)
  exact ⟨Q, hQ, hXQ, hQdim, hQcard.trans (le_trans (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.2 (le_add_of_nonneg_right zero_le_one)) (Nat.cast_nonneg _)) hP)⟩

end ChangFreimanRuzsa
