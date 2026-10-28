/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.Covering.Container
public import ChangFreimanRuzsa.Properization.Iteration
import ChangFreimanRuzsa.Properization.ShortRelations

/-!
# Chang's theorem in `ZMod q`

Let `q` be a prime and let `X : Finset (ZMod q)` satisfy `#(X + X) ≤ κ * #X`. Write `c` for
`containerExponent κ`, `C` for `zmodExponent κ` and `d` for `bohrGAPDim κ`. If `256 * d ≤ #X` and
`exp C * #X ≤ q`, then `X` lies in a `2`-proper generalized arithmetic progression of dimension at
most `c` and of size at most `exp C * #X`.

The proof has two stages. `exists_gap_zmod_subset_dim_le_card_le` puts `X` in a progression of
dimension at most `c` and of size at most `exp c * #X`, and
`exists_twoProperGAP_toFinset_subset_dim_le_card_le_of_injOn_nsmul` replaces that progression by a
`2`-proper one. The second stage holds in every abelian group in which the small multiples of each
nonzero element are distinct. It is stated in that generality as
`exists_twoProperGAP_subset_dim_le_card_le_of_subset_gap`, and `ChangFreimanRuzsa.Int` applies
it to sets of integers.

## Main definitions

* `zmodExponent κ`: the exponent of the bound for the size of the progression.

## Main statements

* `exists_twoProperGAP_subset_dim_le_card_le_of_subset_gap`: the second stage, in a group with no
  small torsion.
* `exists_twoProperGAP_zmod_of_small_sumset`: Chang's theorem in `ZMod q`.
-/

public section

open Finset
open scoped Pointwise

namespace ChangFreimanRuzsa

/-- The exponent `properizationExponent c + c` of the bound for the size of the progression in
Chang's theorem in `ZMod q`, where `c` is `containerExponent κ`. -/
@[expose] noncomputable def zmodExponent (κ : ℝ) : ℝ :=
  properizationExponent (containerExponent κ) + containerExponent κ

/-- The second stage of Chang's theorem, in an abelian group in which the multiples `n • a` with
`n < N` of every nonzero `a` are distinct. Write `c` for `containerExponent κ` and `C` for
`zmodExponent κ`. Let `X` lie in a progression `P` of dimension at most `c` and of size at most
`exp c * #X`. If `exp C * #X ≤ N`, then `X` lies in a `2`-proper progression of dimension at most
`c` and of size at most `exp C * #X`. -/
lemma exists_twoProperGAP_subset_dim_le_card_le_of_subset_gap {G : Type*} [DecidableEq G]
    [AddCommGroup G] {N : ℕ} {κ : ℝ} {X : Finset G} {P : GAP G}
    (hG : ∀ a : G, a ≠ 0 → Set.InjOn (fun n : ℕ ↦ n • a) (Set.Iio N)) (hXP : X ⊆ P.toFinset)
    (hPdim : P.dim ≤ containerExponent κ)
    (hPcard : #P.toFinset ≤ Real.exp (containerExponent κ) * #X)
    (hN : Real.exp (zmodExponent κ) * #X ≤ N) :
    ∃ Q : GAP G, (Q + Q).Proper ∧ X ⊆ Q.toFinset ∧ Q.dim ≤ containerExponent κ ∧
      #Q.toFinset ≤ Real.exp (zmodExponent κ) * #X := by
  have hP : Real.exp (properizationExponent P.dim) * #P.toFinset ≤
      Real.exp (zmodExponent κ) * #X := by
    rw [zmodExponent, Real.exp_add, mul_assoc]
    gcongr
    exact properizationExponent_mono (Nat.cast_nonneg _) hPdim
  obtain ⟨Q, hQ, hPQ, hQdim, hQcard⟩ :=
    exists_twoProperGAP_toFinset_subset_dim_le_card_le_of_injOn_nsmul P hG (hP.trans hN)
  exact ⟨Q, hQ, hXP.trans hPQ, (Nat.cast_le.2 hQdim).trans hPdim, hQcard.trans hP⟩

/-- **Chang's theorem** in `ZMod q` for a prime `q`. Write `c` for `containerExponent κ`, `C` for
`zmodExponent κ` and `d` for `bohrGAPDim κ`. A set `X` with `#(X + X) ≤ κ * #X`, `256 * d ≤ #X`
and `exp C * #X ≤ q` is contained in a `2`-proper generalized arithmetic progression of dimension
at most `c` and of size at most `exp C * #X`. -/
theorem exists_twoProperGAP_zmod_of_small_sumset {q : ℕ} {κ : ℝ} (X : Finset (ZMod q))
    (hq : q.Prime) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X)
    (hXlower : 256 * (bohrGAPDim κ : ℝ) ≤ #X)
    (hXupper : Real.exp (zmodExponent κ) * #X ≤ q) :
    ∃ Q : GAP (ZMod q), (Q + Q).Proper ∧ X ⊆ Q.toFinset ∧ Q.dim ≤ containerExponent κ ∧
      #Q.toFinset ≤ Real.exp (zmodExponent κ) * #X := by
  obtain ⟨P, hXP, hPdim, hPcard⟩ := exists_gap_zmod_subset_dim_le_card_le X hq hκ hXX hXlower
  exact exists_twoProperGAP_subset_dim_le_card_le_of_subset_gap
    (fun _ ↦ GAP.injOn_nsmul_of_prime hq) hXP hPdim hPcard hXupper

end ChangFreimanRuzsa
