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

Let $q$ be a prime and let $X \subseteq \mathbb{Z}/q\mathbb{Z}$ satisfy $|X + X| \le \kappa |X|$.
Write $c_\kappa$ for `containerExponent κ` and $C_\kappa$ for `zmodExponent κ`. If
$e^{c_\kappa} < |X|$ and $e^{C_\kappa} |X| \le q$, then $X$ lies in a $2$-proper generalized
arithmetic progression of dimension at most $c_\kappa$ and of size at most $e^{C_\kappa} |X|$.

The proof has two stages. `exists_gap_zmod_subset_dim_le_card_le` puts $X$ in a progression of
dimension at most $c_\kappa$ and of size at most $e^{c_\kappa} |X|$, and
`exists_twoProperGAP_carrier_subset_dim_le_card_le_of_injOn_nsmul` replaces that progression by a
$2$-proper one. The second stage holds in every abelian group in which the small multiples of each
nonzero element are distinct. It is stated in that generality as
`exists_twoProperGAP_subset_dim_le_card_le_of_subset_gap`, and `ChangFreimanRuzsa.Integers` applies
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

/-- The exponent of the bound for the size of the progression in Chang's theorem in `ZMod q`. -/
@[expose] noncomputable def zmodExponent (κ : ℝ) : ℝ :=
  properizationConstant * (containerExponent κ + 2) ^ 4 + containerExponent κ

/-- The second stage of Chang's theorem, in an abelian group in which the multiples $n a$ with
$n < N$ of every nonzero $a$ are distinct. Write $c_\kappa$ for `containerExponent κ` and
$C_\kappa$ for `zmodExponent κ`. Let $X$ lie in a progression $P$ of dimension at most
$c_\kappa$ and of size at most $e^{c_\kappa} |X|$. If $e^{C_\kappa} |X| \le N$, then $X$ lies in a
$2$-proper progression of dimension at most $c_\kappa$ and of size at most $e^{C_\kappa} |X|$. -/
lemma exists_twoProperGAP_subset_dim_le_card_le_of_subset_gap {G : Type*} [DecidableEq G]
    [AddCommGroup G] {N : ℕ} {κ : ℝ} {X : Finset G} {P : GAP G}
    (hG : ∀ a : G, a ≠ 0 → Set.InjOn (fun n : ℕ ↦ n • a) (Set.Iio N)) (hXP : X ⊆ P.carrier)
    (hPdim : (P.dim : ℝ) ≤ containerExponent κ)
    (hPcard : (#P.carrier : ℝ) ≤ Real.exp (containerExponent κ) * #X)
    (hN : Real.exp (zmodExponent κ) * #X ≤ N) :
    ∃ Q : GAP G, Q.TwoProper ∧ X ⊆ Q.carrier ∧ (∀ i, 1 < Q.length i) ∧
      (Q.dim : ℝ) ≤ containerExponent κ ∧
      (#Q.carrier : ℝ) ≤ Real.exp (zmodExponent κ) * #X := by
  have hP : Real.exp (properizationConstant * ((P.dim : ℝ) + 2) ^ 4) * #P.carrier ≤
      Real.exp (zmodExponent κ) * #X := by
    rw [zmodExponent, Real.exp_add, mul_assoc]
    gcongr
    exact properizationConstant_pos.le
  obtain ⟨Q, hQ, hPQ, hlen, hQdim, hQcard⟩ :=
    exists_twoProperGAP_carrier_subset_dim_le_card_le_of_injOn_nsmul P hG (hP.trans hN)
  exact ⟨Q, hQ, hXP.trans hPQ, hlen, (Nat.cast_le.2 hQdim).trans hPdim, hQcard.trans hP⟩

/-- **Chang's theorem** in `ZMod q` for a prime $q$. Write $c_\kappa$ for
`containerExponent κ` and $C_\kappa$ for `zmodExponent κ`. A set $X$ with
$|X + X| \le \kappa |X|$, $e^{c_\kappa} < |X|$ and $e^{C_\kappa} |X| \le q$ is contained in a
$2$-proper generalized arithmetic progression of dimension at most $c_\kappa$ and of size at most
$e^{C_\kappa} |X|$. -/
theorem exists_twoProperGAP_zmod_of_small_sumset {q : ℕ} {κ : ℝ} (X : Finset (ZMod q))
    (hq : q.Prime) (hκ : 2 ≤ κ) (hXX : (#(X + X) : ℝ) ≤ κ * #X)
    (hXlower : Real.exp (containerExponent κ) < #X)
    (hXupper : Real.exp (zmodExponent κ) * #X ≤ q) :
    ∃ Q : GAP (ZMod q), Q.TwoProper ∧ X ⊆ Q.carrier ∧ (∀ i, 1 < Q.length i) ∧
      (Q.dim : ℝ) ≤ containerExponent κ ∧
      (#Q.carrier : ℝ) ≤ Real.exp (zmodExponent κ) * #X := by
  obtain ⟨P, hXP, -, hPdim, hPcard⟩ := exists_gap_zmod_subset_dim_le_card_le X hq hκ hXX hXlower
  exact exists_twoProperGAP_subset_dim_le_card_le_of_subset_gap
    (fun _ ↦ GAP.injOn_nsmul_of_prime hq) hXP hPdim hPcard hXupper

end ChangFreimanRuzsa
