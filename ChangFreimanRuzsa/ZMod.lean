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

Let `q` be a prime, let `2 ≤ t` and let `X : Finset (ZMod q)` satisfy `#(X + X) ≤ κ * #X`. Write
`c` for `containerExponent κ`, `C` for `zmodExponent κ + tProperExponent t c` and `d` for
`bohrGAPDim κ`. If `256 * d ≤ #X` and `exp C * #X ≤ q`, then `X` lies in a `t`-proper generalized
arithmetic progression of dimension at most `c` and of size at most `exp C * #X`.

The proof has two stages. `exists_gap_zmod_subset_dim_le_card_le` puts `X` in a progression of
dimension at most `c` and of size at most `exp c * #X`, and
`exists_tProperGAP_toFinset_subset_dim_le_card_le_of_injOn_nsmul` replaces that progression by a
`t`-proper one. The second stage holds in every abelian group in which the small multiples of each
nonzero element are distinct. It is stated in that generality as
`exists_tProperGAP_subset_dim_le_card_le_of_subset_gap`, and `ChangFreimanRuzsa.Int` applies
it to sets of integers.

## Main definitions

* `zmodExponent κ`: the exponent of the bound for the size of the progression for `t = 2`.

## Main statements

* `exists_tProperGAP_subset_dim_le_card_le_of_subset_gap`: the second stage, in a group with no
  small torsion.
* `exists_tProperGAP_zmod_of_small_sumset`: Chang's theorem in `ZMod q`.
-/

public section

open Finset
open scoped Pointwise

namespace ChangFreimanRuzsa

/-- The exponent `properizationExponent c + c` of the bound for the size of the progression in
Chang's theorem in `ZMod q` for `t = 2`, where `c` is `containerExponent κ`. -/
@[expose] noncomputable def zmodExponent (κ : ℝ) : ℝ :=
  properizationExponent (containerExponent κ) + containerExponent κ

/-- The second stage of Chang's theorem, in an abelian group in which the multiples `n • a` with
`n < N` of every nonzero `a` are distinct. Let `2 ≤ t`, write `c` for `containerExponent κ` and `C`
for `zmodExponent κ + tProperExponent t c`. Let `X` lie in a progression `P` of dimension at most
`c` and of size at most `exp c * #X`. If `exp C * #X ≤ N`, then `X` lies in a `t`-proper progression
of dimension at most `c` and of size at most `exp C * #X`. -/
lemma exists_tProperGAP_subset_dim_le_card_le_of_subset_gap {G : Type*} [DecidableEq G]
    [AddCommGroup G] {N t : ℕ} {κ : ℝ} {X : Finset G} {P : GAP G} (ht : 2 ≤ t)
    (hG : ∀ a : G, a ≠ 0 → Set.InjOn (fun n : ℕ ↦ n • a) (Set.Iio N)) (hXP : X ⊆ P.toFinset)
    (hPdim : P.dim ≤ containerExponent κ)
    (hPcard : #P.toFinset ≤ Real.exp (containerExponent κ) * #X)
    (hN : Real.exp (zmodExponent κ + tProperExponent t (containerExponent κ)) * #X ≤ N) :
    ∃ Q : GAP G, (t • Q).Proper ∧ X ⊆ Q.toFinset ∧ Q.dim ≤ containerExponent κ ∧
      #Q.toFinset ≤ Real.exp (zmodExponent κ + tProperExponent t (containerExponent κ)) * #X := by
  have hP : Real.exp (properizationExponent P.dim + tProperExponent t P.dim) * #P.toFinset ≤
      Real.exp (zmodExponent κ + tProperExponent t (containerExponent κ)) * #X := by
    rw [zmodExponent, add_right_comm, Real.exp_add _ (containerExponent κ), mul_assoc]
    gcongr
    · exact properizationExponent_mono (Nat.cast_nonneg _) hPdim
    · exact tProperExponent_mono ht (Nat.cast_nonneg _) hPdim
  obtain ⟨Q, hQ, hPQ, hQdim, hQcard⟩ :=
    exists_tProperGAP_toFinset_subset_dim_le_card_le_of_injOn_nsmul P ht hG (hP.trans hN)
  exact ⟨Q, hQ, hXP.trans hPQ, (Nat.cast_le.2 hQdim).trans hPdim, hQcard.trans hP⟩

/-- **Chang's theorem** in `ZMod q` for a prime `q`. Let `2 ≤ t`, write `c` for
`containerExponent κ`, `C` for `zmodExponent κ + tProperExponent t c` and `d` for `bohrGAPDim κ`.
A set `X` with `#(X + X) ≤ κ * #X`, `256 * d ≤ #X` and `exp C * #X ≤ q` is contained in a `t`-proper
generalized arithmetic progression of dimension at most `c` and of size at most `exp C * #X`. -/
theorem exists_tProperGAP_zmod_of_small_sumset {q t : ℕ} {κ : ℝ} (X : Finset (ZMod q))
    (hq : q.Prime) (ht : 2 ≤ t) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X)
    (hXlower : 256 * (bohrGAPDim κ : ℝ) ≤ #X)
    (hXupper : Real.exp (zmodExponent κ + tProperExponent t (containerExponent κ)) * #X ≤ q) :
    ∃ Q : GAP (ZMod q), (t • Q).Proper ∧ X ⊆ Q.toFinset ∧ Q.dim ≤ containerExponent κ ∧
      #Q.toFinset ≤ Real.exp (zmodExponent κ + tProperExponent t (containerExponent κ)) * #X := by
  obtain ⟨P, hXP, hPdim, hPcard⟩ := exists_gap_zmod_subset_dim_le_card_le X hq hκ hXX hXlower
  exact exists_tProperGAP_subset_dim_le_card_le_of_subset_gap ht
    (fun _ ↦ GAP.injOn_nsmul_of_prime hq) hXP hPdim hPcard hXupper

end ChangFreimanRuzsa
