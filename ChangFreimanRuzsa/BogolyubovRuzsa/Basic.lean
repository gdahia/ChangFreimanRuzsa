/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import APAP.Prereqs.Chang
public import ChangFreimanRuzsa.GAP.Defs
public import Mathlib.Combinatorics.Additive.FreimanHom
import ChangFreimanRuzsa.BogolyubovRuzsa.BohrSet
import ChangFreimanRuzsa.BogolyubovRuzsa.Fourier
import ChangFreimanRuzsa.BogolyubovRuzsa.RuzsaModel
import ChangFreimanRuzsa.GAP.FreimanHom
import Mathlib.Tactic.Positivity.Finset

/-!
# The Bogolyubov–Ruzsa lemma in `ZMod q`

Let `q` be prime and let `X : Finset (ZMod q)` satisfy `#(X + X) ≤ κ * #X`. If `#X` is large in
terms of `κ`, then `X + X - (X + X)` contains a proper GAP whose dimension, and whose size relative
to `#X`, are bounded in terms of `κ` alone. The proof follows Chang's argument.

1. (`exists_subset_isAddFreimanIso_eight_card_le`) Ruzsa's model lemma gives a subset `X₁ ⊆ X`
   with `#X ≤ 8 * #X₁` and a Freiman `8`-isomorphic copy `Y : Finset (ZMod m)` of `X₁` with
   `m ≤ 8 * κ ^ 16 * #Y` and `#(Y + Y) ≤ 8 * κ * #Y`.
2. (`exists_card_le_deltaBound_chordSet_subset`) Chang's lemma in `ZMod m` gives a set `Δ` of
   characters whose size is bounded in terms of `κ` and whose Bohr set lies in
   `Y + Y - (Y + Y)`.
3. (`exists_proper_gap_chordSet_card_le`) The Bohr set of `Δ` contains a proper progression `Q`
   of dimension `d = #Δ + 1` with `m ≤ (8 * d) ^ (3 * d) * #Q.carrier` (`bohrLoss`).
4. (`exists_proper_gap_subset_add_sub_add_of_isAddFreimanIso`) The Freiman isomorphism carries
   `Q` to a proper progression `Q₁` of `ZMod q` in `X₁ + X₁ - (X₁ + X₁)` with the same dimension
   and cardinality.

The set `X` only has to have `256 * d` elements, where `d` is `bohrGAPDim κ`, for `ZMod m` to
contain a Bohr progression.

## Main definitions

* `deltaBound κ`, `bohrGAPDim κ` and `bohrLoss d`: the bounds on the size of `Δ`, on the dimension
  of `Q` and on the loss `m / #Q.carrier`.

## Main statements

* `exists_proper_gap_zmod_subset_add_sub_add_card_le`: steps 1 to 4.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open Finset
open scoped Pointwise

noncomputable section

/-! ## The bounds

Each definition is an explicit function of `κ` bounding one quantity of the argument. None of
them is optimal.
-/

/-- The bound on the size of the dissociated set `Δ` given by Chang's lemma in `ZMod m`. It is the
bound of `exists_card_le_largeSpec_subset_addSpan` at the threshold `η ^ 2 = (64 * κ)⁻¹` and the
density `(8 * κ ^ 16)⁻¹ ≤ #Y / m`. -/
def deltaBound (κ : ℝ) : ℕ :=
  ⌈changConst * Real.exp 1 * (⌈1 + Real.log (8 * κ ^ 16)⌉₊ : ℝ) * (8 * (8 * κ))⌉₊

/-- The bound on the dimension `#Δ + 1` of the Bohr progression `Q` and of its image `Q₁` in
`ZMod q`. -/
def bohrGAPDim (κ : ℝ) : ℕ := deltaBound κ + 1

/-- The factor `(8 * d) ^ (3 * d)` lost when passing from `ZMod m` to a Bohr progression of
dimension at most `d`: the progression `Q` satisfies `m ≤ (8 * d) ^ (3 * d) * #Q.carrier`. -/
def bohrLoss (d : ℕ) : ℝ := (8 * d) ^ (3 * d)

lemma bohrLoss_pos {d : ℕ} (hd : 1 ≤ d) : 0 < bohrLoss d :=
  pow_pos (by linarith [(Nat.one_le_cast.2 hd : (1 : ℝ) ≤ d)]) _

lemma log_bohrLoss (d : ℕ) : Real.log (bohrLoss d) = 3 * d * Real.log (8 * d) := by
  rw [bohrLoss, Real.log_pow]
  push_cast
  ring

lemma one_le_bohrGAPDim (κ : ℝ) : 1 ≤ bohrGAPDim κ := Nat.le_add_left 1 _

lemma log_eight_mul_bohrGAPDim_nonneg (κ : ℝ) : 0 ≤ Real.log (8 * bohrGAPDim κ) :=
  Real.log_nonneg (by linarith [(Nat.one_le_cast.2 (one_le_bohrGAPDim κ) : (1 : ℝ) ≤ bohrGAPDim κ)])

/-- A set with at least `256 * bohrGAPDim κ` elements is nonempty. -/
lemma nonempty_of_mul_bohrGAPDim_le {G : Type*} {X : Finset G} {κ : ℝ}
    (hX : 256 * (bohrGAPDim κ : ℝ) ≤ X.card) : X.Nonempty := by
  have hd : (1 : ℝ) ≤ bohrGAPDim κ := by exact_mod_cast one_le_bohrGAPDim κ
  exact card_pos.1 (by exact_mod_cast (by linarith : (0 : ℝ) < X.card))

/-! ## A proper progression in a set of small doubling -/

/-- Ruzsa's model lemma with the bounds used in Chang's argument. If `X : Finset (ZMod q)`
satisfies `#(X + X) ≤ κ * #X`, then there are a subset `X₁ ⊆ X` with `#X ≤ 8 * #X₁` and a Freiman
`8`-isomorphism `φ` from `X₁` onto `Y = X₁.image φ` in `ZMod m` with `#X ≤ 8 * m`,
`m ≤ 8 * κ ^ 16 * #Y` and `#(Y + Y) ≤ 8 * κ * #Y`. -/
lemma exists_subset_isAddFreimanIso_eight_card_le {q : ℕ} {κ : ℝ} (hq : q.Prime) (hκ : 0 ≤ κ)
    {X : Finset (ZMod q)} (hX : X.Nonempty) (hXX : #(X + X) ≤ κ * #X) :
    ∃ (m : ℕ) (X₁ : Finset (ZMod q)) (φ : ZMod q → ZMod m), 0 < m ∧ X₁ ⊆ X ∧ #X ≤ 8 * #X₁ ∧
      IsAddFreimanIso 8 (X₁ : Set (ZMod q)) (X₁.image φ : Set (ZMod m)) φ ∧ (#X : ℝ) ≤ 8 * m ∧
      m ≤ 8 * κ ^ 16 * #(X₁.image φ) ∧ #(X₁.image φ + X₁.image φ) ≤ 8 * κ * #(X₁.image φ) := by
  obtain ⟨m, X₁, φ, hm, hmX, hX₁X, hX₁, hφ⟩ :=
    exists_subset_card_le_mul_card_isAddFreimanIso_of_card_add_le (s := 8) hq (by norm_num) hX hXX
  have : NeZero m := ⟨hm.ne'⟩
  have hY : #(X₁.image φ) = #X₁ := card_image_of_injOn hφ.bijOn.injOn
  have hX₁R : (#X : ℝ) ≤ 8 * #X₁ := by exact_mod_cast hX₁
  refine ⟨m, X₁, φ, hm, hX₁X, hX₁, hφ, ?_, ?_, ?_⟩
  · have hYm : (#X₁ : ℝ) ≤ m := by
      exact_mod_cast hY ▸ (card_le_univ (X₁.image φ)).trans_eq (ZMod.card m)
    linarith
  · norm_num at hmX
    rw [hY]
    nlinarith [pow_nonneg hκ 16]
  · have h : (#(X₁.image φ + X₁.image φ) : ℝ) ≤ #(X + X) := by
      exact_mod_cast (card_add_le_of_isAddFreimanIso
        (IsAddFreimanIso.mono (hmn := by norm_num) hφ.invFunOn)).trans
          (card_le_card (add_subset_add hX₁X hX₁X))
    rw [hY]
    nlinarith

/-- Chang's lemma in the model. If `Y : Finset (ZMod m)` satisfies `m ≤ 8 * κ ^ 16 * #Y` and
`#(Y + Y) ≤ 8 * κ * #Y`, then there is a set `Δ` of at most `deltaBound κ` characters such that
every `x` with `‖1 - ψ x‖ ≤ (4 * (#Δ + 1))⁻¹` for all `ψ ∈ Δ` lies in `Y + Y - (Y + Y)`. -/
lemma exists_card_le_deltaBound_chordSet_subset {m : ℕ} [NeZero m] {κ : ℝ} (hκ : 2 ≤ κ)
    {Y : Finset (ZMod m)} (hY : Y.Nonempty) (hYm : m ≤ 8 * κ ^ 16 * #Y)
    (hYY : #(Y + Y) ≤ 8 * κ * #Y) :
    ∃ Δ : Finset (AddChar (ZMod m) ℂ), #Δ ≤ deltaBound κ ∧
      {x | ∀ ψ ∈ Δ, ‖1 - ψ x‖ ≤ ((4 : ℝ) * (#Δ + 1))⁻¹} ⊆
        ((Y + Y) - (Y + Y) : Finset (ZMod m)) := by
  obtain ⟨Δ, -, hΔ, hspan⟩ := exists_card_le_largeSpec_subset_addSpan hY
    (η := Real.sqrt ((8 * (8 * κ))⁻¹)) (Real.sqrt_pos.2 (by positivity))
  refine ⟨Δ, hΔ.trans (Nat.ceil_le_ceil ?_),
    fun _ hx ↦ mem_add_sub_add_of_largeSpec_subset_addSpan (by linarith) hY hYY hspan hx⟩
  rw [Real.sq_sqrt (by positivity), div_inv_eq_mul]
  have hY₀ : (0 : ℝ) < #Y := by exact_mod_cast hY.card_pos
  gcongr
  · exact inv_pos.2 (div_pos hY₀ (Nat.cast_pos.2 (NeZero.pos m)))
  · rw [inv_div, div_le_iff₀ hY₀]
    exact hYm

/-- The dimensional factor of `exists_proper_gap_chordSet`, together with the reciprocal of the
chord width, is at most `(8 * (k + 1)) ^ (3 * (k + 1))`, where `k = #Δ`. -/
private lemma pow_mul_pow_le (k : ℕ) :
    (4 * ((k : ℝ) + 1)) ^ (2 * (k + 1)) * (8 * Real.pi * ((k : ℝ) + 1)) ^ k ≤
      (8 * ((k : ℝ) + 1)) ^ (3 * (k + 1)) := by
  refine (mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (by positivity)
    (?_ : 8 * Real.pi * ((k : ℝ) + 1) ≤ 32 * (k + 1)) k).trans
      (pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) k.le_succ))
        (by positivity)).trans_eq ?_
  · nlinarith [mul_le_mul_of_nonneg_right Real.pi_le_four (by positivity : (0 : ℝ) ≤ k + 1)]
  · rw [pow_mul, pow_mul, ← mul_pow]
    ring

/-- The Bohr set `{x | ∀ ψ ∈ Δ, ‖1 - ψ x‖ ≤ (4 * (#Δ + 1))⁻¹}` in `ZMod m` contains a proper
progression `Q` of dimension at most `d` with `m ≤ bohrLoss d * #Q.carrier`, provided `#Δ < d` and
`32 * d ≤ m`. -/
lemma exists_proper_gap_chordSet_card_le {m d : ℕ} [NeZero m] (Δ : Finset (AddChar (ZMod m) ℂ))
    (hΔ : #Δ + 1 ≤ d) (hm : 32 * (d : ℝ) ≤ m) :
    ∃ Q : GAP (ZMod m), Q.Proper ∧ Q.dim ≤ d ∧
      (Q.carrier : Set (ZMod m)) ⊆ {x | ∀ ψ ∈ Δ, ‖1 - ψ x‖ ≤ ((4 : ℝ) * (#Δ + 1))⁻¹} ∧
      m ≤ bohrLoss d * #Q.carrier := by
  have hΔR : (#Δ : ℝ) + 1 ≤ d := by exact_mod_cast hΔ
  have hε : 2 * Real.pi ≤ ((4 : ℝ) * (#Δ + 1))⁻¹ * m := by
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith [Real.pi_le_four]
  have hε' : ((4 : ℝ) * (#Δ + 1))⁻¹ / (2 * Real.pi) = (8 * Real.pi * (#Δ + 1))⁻¹ := by
    rw [div_eq_mul_inv, ← mul_inv]
    ring
  obtain ⟨Q, hQ, hdim, hsub, hcard⟩ :=
    exists_proper_gap_chordSet Δ hε (inv_le_one_of_one_le₀ (by linarith))
  refine ⟨Q, hQ, hdim.trans hΔ, hsub, ?_⟩
  rw [hε', inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)] at hcard
  refine hcard.trans ?_
  rw [mul_right_comm, bohrLoss]
  gcongr
  exact (pow_mul_pow_le #Δ).trans ((pow_le_pow_left₀ (by positivity) (by linarith) _).trans
    (pow_le_pow_right₀ (by linarith) (by grind)))

/-- Let `q` be prime and let `X : Finset (ZMod q)` satisfy `#(X + X) ≤ κ * #X` and
`256 * d ≤ #X`, where `d` is `bohrGAPDim κ`. Then `X` has a subset `X₁` with `#X ≤ 8 * #X₁`, and
`X + X - (X + X)` contains a proper progression `Q₁` of dimension at most `d` with
`#X ≤ 8 * bohrLoss d * #Q₁.carrier`. -/
lemma exists_proper_gap_zmod_subset_add_sub_add_card_le {q : ℕ} {κ : ℝ} (X : Finset (ZMod q))
    (hq : Nat.Prime q) (hκ : 2 ≤ κ)
    (hXX : (X + X).card ≤ κ * X.card)
    (hXlower : 256 * (bohrGAPDim κ : ℝ) ≤ X.card) :
    ∃ (X₁ : Finset (ZMod q)) (Q₁ : GAP (ZMod q)),
      X₁ ⊆ X ∧ X.card ≤ 8 * X₁.card ∧ Q₁.Proper ∧
        (Q₁.dim : ℝ) ≤ bohrGAPDim κ ∧
        Q₁.carrier ⊆ (X + X) - (X + X) ∧
        X.card ≤ 8 * bohrLoss (bohrGAPDim κ) * Q₁.carrier.card := by
  have hX : X.Nonempty := nonempty_of_mul_bohrGAPDim_le hXlower
  obtain ⟨m, X₁, φ, hm, hX₁X, hX₁, hφ, hXm, hmY, hYY⟩ :=
    exists_subset_isAddFreimanIso_eight_card_le hq (by linarith) hX hXX
  have : NeZero m := ⟨hm.ne'⟩
  obtain ⟨Δ, hΔ, hchord⟩ := exists_card_le_deltaBound_chordSet_subset hκ
    ((card_pos.1 (by grind [hX.card_pos])).image φ) hmY hYY
  obtain ⟨Q, hQ, hQdim, hQsub, hQcard⟩ := exists_proper_gap_chordSet_card_le Δ
    (d := bohrGAPDim κ) (Nat.add_le_add_right hΔ 1)
    (by linarith)
  obtain ⟨Q₁, hQ₁, hQ₁dim, hQ₁card, hQ₁sub⟩ :=
    exists_proper_gap_subset_add_sub_add_of_isAddFreimanIso hφ hQ
      (coe_subset.1 (hQsub.trans hchord))
  refine ⟨X₁, Q₁, hX₁X, hX₁, hQ₁, by exact_mod_cast hQ₁dim.trans hQdim,
    hQ₁sub.trans (by gcongr), ?_⟩
  rw [hQ₁card]
  linarith

end

end ChangFreimanRuzsa
