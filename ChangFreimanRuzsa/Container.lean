/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.Packing
public import APAPCompat.Prereqs.Chang
import ChangFreimanRuzsa.BohrProgression
import ChangFreimanRuzsa.Fourier
import ChangFreimanRuzsa.FreimanRigidity
import ChangFreimanRuzsa.RuzsaModel
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Combinatorics.Additive.RuzsaCovering

/-! # A progression containing a set of small doubling

Let $q$ be prime and let $X \subseteq \mathbb{Z}/q\mathbb{Z}$ satisfy $|X + X| \le \kappa |X|$. If
$|X|$ is large in terms of $\kappa$, then $X$ is contained in a (not necessarily proper) GAP whose
dimension, and whose size relative to $|X|$, are bounded in terms of $\kappa$ alone. The proof
follows Chang's argument.

1. (`exists_subset_isAddFreimanIso_eight_card_le`) Ruzsa's model lemma gives a subset
   $X_1 \subseteq X$ with $|X| \le 8 |X_1|$ and a Freiman $8$-isomorphic copy
   $Y \subseteq \mathbb{Z}/m\mathbb{Z}$ of $X_1$ with $m \le 8 \kappa^{16} |Y|$ and
   $|Y + Y| \le 8 \kappa |Y|$.
2. (`exists_card_le_deltaBound_chordSet_subset`) Chang's lemma in $\mathbb{Z}/m\mathbb{Z}$
   gives a set $\Delta$ of characters whose size is bounded in terms of $\kappa$ and whose Bohr
   set lies in $2Y - 2Y$.
3. (`exists_proper_gap_chordSet_card_le`) The Bohr set of $\Delta$ contains a proper
   progression $Q$ of dimension $d = |\Delta| + 1$ with $m \le (8 d)^{3 d} |Q|$ (`bohrLoss`).
4. (`exists_proper_gap_subset_add_sub_add_of_isAddFreimanIso`) The Freiman isomorphism carries
   $Q$ to a proper progression $Q_1 \subseteq 2X_1 - 2X_1$ of $\mathbb{Z}/q\mathbb{Z}$ with the
   same dimension and cardinality.
5. (`exists_length_le_iterationBound_subset_add_sub`) The packing argument adds to $Q_1$ sets
   $S_1, \dots, S_k \subseteq X_1$ of $\lceil 3 \kappa \rceil$ elements until
   $X_1 \subseteq F + (Q' - Q')$ with $|F| \le \lceil 3 \kappa \rceil$, where
   $Q' = Q_1 + S_1 + \dots + S_k$.
6. (`exists_card_le_subset_sub_sub_add`) Let $T = Q' + \Sigma(F)$, where $\Sigma(F)$ is the set
   of subset sums of $F$. It contains $0$ and $F$, so $X_1 \subseteq T - T$
   (`add_sub_subset_add_sub_add`), and Ruzsa's covering lemma gives
   $X \subseteq (T - T) - (T - T) + W$ for a set $W$ of at most $8 \kappa$ elements.
7. (`GAP.packingContainer`) Adding to $Q_1$ one step of length $2$ for each element of the sets
   $S_j$ and of $F$, doubling twice and adding one step of length $2$ for each element of $W$
   gives a progression containing $X$.

Steps 5 to 7, `exists_gap_subset_dim_le_card_le_of_subset_add_sub_add`, hold in every abelian
group, and `Integers.lean` applies them to sets of integers.

All bounds are explicit functions of $\kappa$. They are collected in `containerExponent`, which
bounds the dimension of the progression containing $X$ and the logarithm of its size relative to
$|X|$. The set $X$ only has to have $256 d$ elements, where $d$ is `bohrGAPDim κ`, for
$\mathbb{Z}/m\mathbb{Z}$ to contain a Bohr progression.

## Main statements

* `exists_proper_gap_zmod_subset_add_sub_add_card_le`: steps 1 to 4.
* `exists_gap_subset_dim_le_card_le_of_subset_add_sub_add`: steps 5 to 7, in an arbitrary abelian
  group.
* `exists_gap_zmod_subset_dim_le_card_le`: the progression containing $X$ in
  $\mathbb{Z}/q\mathbb{Z}$.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open Finset
open scoped Pointwise

noncomputable section

/-! ## The bounds

Each definition is an explicit function of $\kappa$ bounding one quantity of the argument. None of
them is optimal.
-/

/-- The bound on the size of the dissociated set $\Delta$ given by Chang's lemma in
$\mathbb{Z}/m\mathbb{Z}$. It is the bound of `exists_card_le_largeSpec_subset_addSpan` at the
threshold $\eta^2 = (64 \kappa)^{-1}$ and the density $|Y| / m \ge (8 \kappa^{16})^{-1}$. -/
def deltaBound (κ : ℝ) : ℕ :=
  ⌈changConst * Real.exp 1 * (⌈1 + Real.log (8 * κ ^ 16)⌉₊ : ℝ) * (8 * (8 * κ))⌉₊

/-- The bound on the dimension $|\Delta| + 1$ of the Bohr progression $Q$ and of its image $Q_1$
in $\mathbb{Z}/q\mathbb{Z}$. -/
def bohrGAPDim (κ : ℝ) : ℕ := deltaBound κ + 1

/-- The factor $(8 d)^{3 d}$ lost when passing from $\mathbb{Z}/m\mathbb{Z}$ to a Bohr progression
of dimension at most $d$: the progression $Q$ satisfies $m \le (8 d)^{3 d} |Q|$. -/
def bohrLoss (d : ℕ) : ℝ := (8 * d) ^ (3 * d)

/-- The number $m = \lceil 3 \kappa \rceil$ of disjoint translates added at each step of the
packing argument. Since $m \ge 3 \kappa$, after $k$ steps the size $|Q_1| m^k$ of the current set
stays below the Plünnecke–Ruzsa bound $\kappa^{k + 4} |X|$ only if $3^k |Q_1| \le \kappa^4 |X|$. -/
def translateCount (κ : ℝ) : ℕ := ⌈3 * κ⌉₊

/-- The bound $3 + 4 \kappa + 3 d \log (8 d)$ on the number of steps of the packing argument, where
$d$ is `bohrGAPDim κ`. It bounds $\log_3$ of $8 \kappa^4$ `bohrLoss d`. -/
def iterationBound (κ : ℝ) : ℝ := 3 + 4 * κ + 3 * bohrGAPDim κ * Real.log (8 * bohrGAPDim κ)

/-- The exponent $E(\kappa)$ of the progression containing $X$. It bounds the dimension of the
progression and the logarithm of its size relative to $|X|$, and $e^{E(\kappa)}$ is at least the
size $256 d$ that $|X|$ has to reach for the Ruzsa model of $X$ to contain a Bohr progression. -/
def containerExponent (κ : ℝ) : ℝ :=
  256 + 3 * bohrGAPDim κ + 12 * κ + 3 * translateCount κ * (iterationBound κ + 1)

lemma bohrLoss_pos {d : ℕ} (hd : 1 ≤ d) : 0 < bohrLoss d :=
  pow_pos (by linarith [(Nat.one_le_cast.2 hd : (1 : ℝ) ≤ d)]) _

lemma log_bohrLoss (d : ℕ) : Real.log (bohrLoss d) = 3 * d * Real.log (8 * d) := by
  rw [bohrLoss, Real.log_pow]
  push_cast
  ring

lemma one_le_bohrGAPDim (κ : ℝ) : 1 ≤ bohrGAPDim κ := Nat.le_add_left 1 _

lemma log_eight_mul_bohrGAPDim_nonneg (κ : ℝ) : 0 ≤ Real.log (8 * bohrGAPDim κ) :=
  Real.log_nonneg (by linarith [(Nat.one_le_cast.2 (one_le_bohrGAPDim κ) : (1 : ℝ) ≤ bohrGAPDim κ)])

lemma iterationBound_nonneg {κ : ℝ} (hκ : 0 ≤ κ) : 0 ≤ iterationBound κ := by
  rw [iterationBound]
  linarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (bohrGAPDim κ))
    (log_eight_mul_bohrGAPDim_nonneg κ)]

lemma containerExponent_pos {κ : ℝ} (hκ : 2 ≤ κ) : 0 < containerExponent κ := by
  rw [containerExponent]
  nlinarith [iterationBound_nonneg (by linarith : 0 ≤ κ), Nat.cast_nonneg (α := ℝ) (bohrGAPDim κ),
    Nat.cast_nonneg (α := ℝ) (translateCount κ)]

/-- The exponent bounds the dimension of the progression containing $X$. -/
lemma mul_add_bohrGAPDim_add_le_containerExponent {κ : ℝ} (hκ : 2 ≤ κ) :
    8 * κ + bohrGAPDim κ + translateCount κ * (iterationBound κ + 1) ≤ containerExponent κ := by
  rw [containerExponent]
  nlinarith [iterationBound_nonneg (by linarith : 0 ≤ κ), Nat.cast_nonneg (α := ℝ) (bohrGAPDim κ),
    Nat.cast_nonneg (α := ℝ) (translateCount κ)]

/-- The exponent bounds the logarithm of the size of the progression containing $X$ relative to
$|X|$. -/
lemma mul_add_two_mul_bohrGAPDim_add_le_containerExponent (κ : ℝ) :
    8 * κ + 2 * bohrGAPDim κ + 3 * translateCount κ * (iterationBound κ + 1) + 4 * κ ≤
      containerExponent κ := by
  rw [containerExponent]
  linarith [Nat.cast_nonneg (α := ℝ) (bohrGAPDim κ)]

/-- The exponent is at least $256 + d$, where $d$ is `bohrGAPDim κ`. -/
lemma add_bohrGAPDim_le_containerExponent {κ : ℝ} (hκ : 2 ≤ κ) :
    256 + bohrGAPDim κ ≤ containerExponent κ := by
  rw [containerExponent]
  nlinarith [iterationBound_nonneg (by linarith : 0 ≤ κ), Nat.cast_nonneg (α := ℝ) (bohrGAPDim κ),
    Nat.cast_nonneg (α := ℝ) (translateCount κ)]

/-- A set with at least $256 d$ elements, where $d$ is `bohrGAPDim κ`, is nonempty. -/
lemma nonempty_of_mul_bohrGAPDim_le {G : Type*} {X : Finset G} {κ : ℝ}
    (hX : 256 * (bohrGAPDim κ : ℝ) ≤ X.card) : X.Nonempty := by
  have hd : (1 : ℝ) ≤ bohrGAPDim κ := by exact_mod_cast one_le_bohrGAPDim κ
  exact card_pos.1 (by exact_mod_cast (by linarith : (0 : ℝ) < X.card))

/-- If $x > e^{E(\kappa)}$, then $x \ge 256 d$, where $d$ is `bohrGAPDim κ`. -/
lemma mul_bohrGAPDim_le_of_exp_lt {κ x : ℝ} (hκ : 2 ≤ κ)
    (hx : Real.exp (containerExponent κ) < x) : 256 * bohrGAPDim κ ≤ x := by
  refine le_trans ?_ ((Real.exp_le_exp.2 (add_bohrGAPDim_le_containerExponent hκ)).trans hx.le)
  rw [Real.exp_add]
  nlinarith [Real.add_one_le_exp (256 : ℝ), Real.add_one_le_exp (bohrGAPDim κ : ℝ),
    Real.exp_pos (bohrGAPDim κ : ℝ), Real.exp_pos (256 : ℝ),
    Nat.cast_nonneg (α := ℝ) (bohrGAPDim κ)]

/-! ## A proper progression in a set of small doubling -/

/-- Ruzsa's model lemma with the bounds used in Chang's argument. If
$X \subseteq \mathbb{Z}/q\mathbb{Z}$ satisfies $|X + X| \le \kappa |X|$, then there are a subset
$X_1 \subseteq X$ with $|X| \le 8 |X_1|$ and a Freiman $8$-isomorphism $\varphi$ from $X_1$ onto
$Y = \varphi(X_1) \subseteq \mathbb{Z}/m\mathbb{Z}$ with $|X| \le 8m$, $m \le 8 \kappa^{16} |Y|$ and
$|Y + Y| \le 8 \kappa |Y|$. -/
lemma exists_subset_isAddFreimanIso_eight_card_le {q : ℕ} {κ : ℝ} (hq : q.Prime) (hκ : 0 ≤ κ)
    {X : Finset (ZMod q)} (hX : X.Nonempty) (hXX : (#(X + X) : ℝ) ≤ κ * #X) :
    ∃ (m : ℕ) (X₁ : Finset (ZMod q)) (φ : ZMod q → ZMod m), 0 < m ∧ X₁ ⊆ X ∧ #X ≤ 8 * #X₁ ∧
      IsAddFreimanIso 8 (X₁ : Set (ZMod q)) (X₁.image φ : Set (ZMod m)) φ ∧ (#X : ℝ) ≤ 8 * m ∧
      (m : ℝ) ≤ 8 * κ ^ 16 * #(X₁.image φ) ∧
      (#(X₁.image φ + X₁.image φ) : ℝ) ≤ 8 * κ * #(X₁.image φ) := by
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

/-- Chang's lemma in the model. If $Y \subseteq \mathbb{Z}/m\mathbb{Z}$ satisfies
$m \le 8 \kappa^{16} |Y|$ and $|Y + Y| \le 8 \kappa |Y|$, then there is a set $\Delta$ of at most
`deltaBound κ` characters such that every $x$ with $|1 - \psi(x)| \le (4(|\Delta| + 1))^{-1}$
for all $\psi \in \Delta$ lies in $2Y - 2Y$. -/
lemma exists_card_le_deltaBound_chordSet_subset {m : ℕ} [NeZero m] {κ : ℝ} (hκ : 2 ≤ κ)
    {Y : Finset (ZMod m)} (hY : Y.Nonempty) (hYm : (m : ℝ) ≤ 8 * κ ^ 16 * #Y)
    (hYY : (#(Y + Y) : ℝ) ≤ 8 * κ * #Y) :
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
chord width, is at most $(8 (k + 1))^{3 (k + 1)}$, where $k = |\Delta|$. -/
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

/-- The Bohr set $\{x : |1 - \psi(x)| \le (4(|\Delta| + 1))^{-1}$ for all
$\psi \in \Delta\}$ in $\mathbb{Z}/m\mathbb{Z}$ contains a proper progression $Q$ of dimension at
most $d$ with $m \le$ `bohrLoss d` $\cdot |Q|$, provided $|\Delta| < d$ and $m \ge 32 d$. -/
lemma exists_proper_gap_chordSet_card_le {m d : ℕ} [NeZero m] (Δ : Finset (AddChar (ZMod m) ℂ))
    (hΔ : #Δ + 1 ≤ d) (hm : 32 * (d : ℝ) ≤ m) :
    ∃ Q : GAP (ZMod m), Q.Proper ∧ Q.dim ≤ d ∧
      (Q.carrier : Set (ZMod m)) ⊆ {x | ∀ ψ ∈ Δ, ‖1 - ψ x‖ ≤ ((4 : ℝ) * (#Δ + 1))⁻¹} ∧
      (m : ℝ) ≤ bohrLoss d * #Q.carrier := by
  have hΔR : (#Δ : ℝ) + 1 ≤ d := by exact_mod_cast hΔ
  have hε : 2 * Real.pi ≤ ((4 : ℝ) * (#Δ + 1))⁻¹ * m := by
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith [Real.pi_le_four]
  have hε' : ((4 : ℝ) * (#Δ + 1))⁻¹ / (2 * Real.pi) = (8 * Real.pi * (#Δ + 1))⁻¹ := by
    rw [div_eq_mul_inv, ← mul_inv]
    ring
  obtain ⟨Q, hQ, hdim, hsub, hcard⟩ :=
    exists_proper_gap_chordSet Δ hε (inv_le_one_of_one_le₀ (by linarith))
  refine ⟨Q, hQ, hdim.trans_le hΔ, hsub, ?_⟩
  rw [hε', inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)] at hcard
  refine hcard.trans ?_
  rw [mul_right_comm, bohrLoss]
  gcongr
  exact (pow_mul_pow_le #Δ).trans ((pow_le_pow_left₀ (by positivity) (by linarith) _).trans
    (pow_le_pow_right₀ (by linarith) (by grind)))

/-- Let $q$ be prime and let $X \subseteq \mathbb{Z}/q\mathbb{Z}$ satisfy $|X + X| \le \kappa |X|$
and $|X| \ge 256 d$, where $d$ is `bohrGAPDim κ`. Then $X$ has a subset $X_1$ with
$|X| \le 8 |X_1|$, and $2X - 2X$ contains a proper progression $Q_1$ of dimension at most $d$ with
$|X| \le 8$ `bohrLoss d` $\cdot |Q_1|$. -/
lemma exists_proper_gap_zmod_subset_add_sub_add_card_le {q : ℕ} {κ : ℝ} (X : Finset (ZMod q))
    (hq : Nat.Prime q) (hκ : 2 ≤ κ)
    (hXX : ((X + X).card : ℝ) ≤ κ * X.card)
    (hXlower : 256 * (bohrGAPDim κ : ℝ) ≤ X.card) :
    ∃ (X₁ : Finset (ZMod q)) (Q₁ : GAP (ZMod q)),
      X₁ ⊆ X ∧ X.card ≤ 8 * X₁.card ∧ Q₁.Proper ∧
        (Q₁.dim : ℝ) ≤ bohrGAPDim κ ∧
        Q₁.carrier ⊆ (X + X) - (X + X) ∧
        (X.card : ℝ) ≤ 8 * bohrLoss (bohrGAPDim κ) * Q₁.carrier.card := by
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
  refine ⟨X₁, Q₁, hX₁X, hX₁, hQ₁, by exact_mod_cast hQ₁dim.trans_le hQdim,
    hQ₁sub.trans (by gcongr), ?_⟩
  rw [hQ₁card]
  linarith

/-! ## The packing argument -/

section Packing

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-- If $Q \subseteq 2X - 2X$ and $S_1, \dots, S_k \subseteq X$, then
$Q + S_1 + \dots + S_k \subseteq (k + 2)X - 2X$. -/
lemma add_sum_subset_nsmul_sub_nsmul {X Q : Finset G} {l : List (Finset G)}
    (hQ : Q ⊆ X + X - (X + X)) (hl : ∀ S ∈ l, S ⊆ X) :
    Q + l.sum ⊆ (l.length + 2) • X - 2 • X := by
  rw [add_nsmul, add_comm (l.length • X), ← sub_add_eq_add_sub, two_nsmul]
  exact add_subset_add hQ (List.sum_le_length_nsmul l X hl)

/-- If $Q \subseteq 2X - 2X$ and $|Q + S_1 + \dots + S_k| = |Q| m^k$ for sets $S_j \subseteq X$
and some $m \ge 3\kappa$, then $3^k |Q| \le \kappa^4 |X|$ by the Plünnecke–Ruzsa inequality. -/
lemma three_pow_mul_card_le {X Q : Finset G} {l : List (Finset G)} {κ : ℝ} {m : ℕ}
    (hX : X.Nonempty) (hκ : 0 < κ) (hm : 3 * κ ≤ m) (hXX : (#(X + X) : ℝ) ≤ κ * #X)
    (hQ : Q ⊆ X + X - (X + X)) (hl : ∀ S ∈ l, S ⊆ X)
    (hcard : #(Q + l.sum) = #Q * m ^ l.length) :
    (3 : ℝ) ^ l.length * #Q ≤ κ ^ 4 * #X := by
  have hPR : (#((l.length + 2) • X - 2 • X) : ℝ) ≤ κ ^ (l.length + 4) * #X := by
    have h := (NNRat.cast_le (K := ℝ)).2
      (pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hX X (l.length + 2) 2)
    push_cast [NNRat.cast_pow] at h
    refine h.trans ?_
    gcongr
    exact (div_le_iff₀ (by exact_mod_cast hX.card_pos)).2 hXX
  refine le_of_mul_le_mul_right ?_ (pow_pos hκ l.length)
  calc (3 : ℝ) ^ l.length * #Q * κ ^ l.length = #Q * (3 * κ) ^ l.length := by ring
    _ ≤ #Q * m ^ l.length := by gcongr
    _ = #(Q + l.sum) := by exact_mod_cast hcard.symm
    _ ≤ #((l.length + 2) • X - 2 • X) := by
      exact_mod_cast card_le_card (add_sum_subset_nsmul_sub_nsmul hQ hl)
    _ ≤ κ ^ (l.length + 4) * #X := hPR
    _ = κ ^ 4 * #X * κ ^ l.length := by ring

/-- If $3^k \le 8 \kappa^4$ `bohrLoss d`, where $d$ is `bohrGAPDim κ`, then $k$ is at most
`iterationBound κ`. -/
lemma le_iterationBound_of_three_pow_le {κ : ℝ} (hκ : 0 < κ) {k : ℕ}
    (h : (3 : ℝ) ^ k ≤ 8 * κ ^ 4 * bohrLoss (bohrGAPDim κ)) :
    (k : ℝ) ≤ iterationBound κ := by
  have hlog := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_mul (by positivity) (bohrLoss_pos (one_le_bohrGAPDim κ)).ne',
    Real.log_mul (by norm_num) (by positivity), Real.log_pow, log_bohrLoss] at hlog
  have hl3 : (1 : ℝ) ≤ Real.log 3 := by
    simpa using Real.log_le_log (Real.exp_pos 1)
      (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ 3)
  have hl8 : Real.log 8 ≤ 3 := by
    rw [(by norm_num : (8 : ℝ) = 2 ^ 3), Real.log_pow]
    push_cast
    linarith [Real.log_two_lt_d9]
  push_cast at hlog
  rw [iterationBound]
  linarith [mul_le_mul_of_nonneg_left hl3 (Nat.cast_nonneg (α := ℝ) k), Real.log_le_self hκ.le]

/-- The packing step of Chang's argument. Let $X_1 \subseteq X$ with $|X + X| \le \kappa |X|$, and
let $Q \subseteq 2X - 2X$ be nonempty with $|X| \le 8$ `bohrLoss d` $\cdot |Q|$, where $d$ is
`bohrGAPDim κ`. Then $|Q| \le \kappa^4 |X|$, and there are sets
$S_1, \dots, S_k \subseteq X_1$ of size $m$ = `translateCount κ`, with
$k \le$ `iterationBound κ`, and a set $F$ of at most $m$ elements with
$X_1 \subseteq F + (Q' - Q')$, where $Q' = Q + S_1 + \dots + S_k$. -/
lemma exists_length_le_iterationBound_subset_add_sub {X X₁ Q : Finset G} {κ : ℝ}
    (hX : X.Nonempty) (hκ : 0 < κ) (hXX : (#(X + X) : ℝ) ≤ κ * #X) (hX₁X : X₁ ⊆ X)
    (hQ : Q.Nonempty) (hQX : Q ⊆ X + X - (X + X))
    (hXQ : (#X : ℝ) ≤ 8 * bohrLoss (bohrGAPDim κ) * #Q) :
    ∃ (l : List (Finset G)) (F : Finset G), (∀ S ∈ l, S ⊆ X₁ ∧ #S = translateCount κ) ∧
      (l.length : ℝ) ≤ iterationBound κ ∧ (#Q : ℝ) ≤ κ ^ 4 * #X ∧
      #F ≤ translateCount κ ∧ X₁ ⊆ F + (Q + l.sum - (Q + l.sum)) := by
  have hgrow {l : List (Finset G)} (hl : ∀ S ∈ l, S ⊆ X₁ ∧ #S = translateCount κ)
      (hcard : #(Q + l.sum) = #Q * translateCount κ ^ l.length) :
      (3 : ℝ) ^ l.length * #Q ≤ κ ^ 4 * #X := by
    obtain ⟨hlX₁, -⟩ := forall₂_and.1 hl
    exact three_pow_mul_card_le hX hκ (Nat.le_ceil _) hXX hQX
      (fun S hS ↦ (hlX₁ S hS).trans hX₁X) hcard
  have hQ₁ : (1 : ℝ) ≤ #Q := by exact_mod_cast hQ.card_pos
  have hB (l : List (Finset G)) (hl : ∀ S ∈ l, S ⊆ X₁ ∧ #S = translateCount κ)
      (hcard : #(Q + l.sum) = #Q * translateCount κ ^ l.length) :
      l.length ≤ ⌈κ ^ 4 * #X⌉₊ := by
    exact_mod_cast (by exact_mod_cast (Nat.lt_pow_self (by norm_num : 1 < 3)).le :
      (l.length : ℝ) ≤ 3 ^ l.length).trans ((le_mul_of_one_le_right (by positivity) hQ₁).trans
        ((hgrow hl hcard).trans (Nat.le_ceil _)))
  obtain ⟨l, F, hl, hcard, -, hF, hcover⟩ :=
    exists_card_add_sum_eq_card_mul_pow_and_subset_add_sub hQ (Nat.ceil_pos.2 (by linarith)) hB
  refine ⟨l, F, hl, le_iterationBound_of_three_pow_le hκ ?_, ?_, hF.le, hcover⟩
  · refine le_of_mul_le_mul_right ((hgrow hl hcard).trans ?_) (by linarith)
    exact (mul_le_mul_of_nonneg_left hXQ (pow_pos hκ 4).le).trans_eq (by ring)
  · nlinarith [hgrow hl hcard, one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3) (n := l.length)]

/-- If $F \subseteq U$ and $0 \in U$, then $F + (S - S) \subseteq (S + U) - (S + U)$. -/
lemma add_sub_subset_add_sub_add {F S U : Finset G} (hFU : F ⊆ U) (hU : 0 ∈ U) :
    F + (S - S) ⊆ S + U - (S + U) := by
  rw [← add_sub_assoc, add_comm F]
  exact sub_subset_sub (add_subset_add_left hFU) (subset_add_left S hU)

/-- Ruzsa's covering step. If $X_1 \subseteq T - T$, $X_1 \subseteq X$, $|X| \le 8 |X_1|$ and
$|X + X| \le \kappa |X|$, then $X \subseteq (T - T) - (T - T) + W$ for a set $W$ of at most
$8 \kappa$ elements. -/
lemma exists_card_le_subset_sub_sub_add {X X₁ T : Finset G} {κ : ℝ}
    (hκ : 0 ≤ κ) (hXX : (#(X + X) : ℝ) ≤ κ * #X) (hX₁ : X₁.Nonempty) (hX₁X : X₁ ⊆ X)
    (hXX₁ : #X ≤ 8 * #X₁) (hcover : X₁ ⊆ T - T) :
    ∃ W : Finset G, (#W : ℝ) ≤ 8 * κ ∧ X ⊆ T - T - (T - T) + W := by
  obtain ⟨W, -, hW, hXW⟩ := ruzsa_covering_add (A := X) (K := 8 * κ) hX₁ (by
    linarith [(Nat.cast_le (α := ℝ)).2 (card_le_card (add_subset_add_left (s := X) hX₁X)),
      mul_le_mul_of_nonneg_left (by exact_mod_cast hXX₁ : (#X : ℝ) ≤ 8 * #X₁) hκ])
  exact ⟨W, hW, hXW.trans ((add_subset_add_left (sub_subset_sub hcover hcover)).trans_eq
    (add_comm _ _))⟩

namespace GAP

/-- The progression of the packing argument. Starting from $Q$, it adds one step of length $2$ for
each entry of $l$, applies `GAP.difference` twice and adds one step of length $2$ for each element
of $W$. If $S \subseteq Q + \sum_{a \in l} \{0, a\}$, then it contains $(S - S) - (S - S) + W$. -/
def packingContainer (Q : GAP G) (l : List G) (W : Finset G) : GAP G :=
  (Q.consBinaryList l).difference.difference.consBinaryList W.toList

lemma sub_sub_add_subset_packingContainer {Q : GAP G} {l : List G} {S : Finset G}
    (hS : S ⊆ Q.carrier + listSubsetSum l) (W : Finset G) :
    S - S - (S - S) + W ⊆ (Q.packingContainer l W).carrier :=
  add_subset_consBinaryList_toList (sub_subset_difference_of_subset
    (sub_subset_difference_of_subset (hS.trans (Q.add_listSubsetSum_subset_consBinaryList l)))) W

lemma one_lt_length_packingContainer (Q : GAP G) (l : List G) (W : Finset G)
    (i : Fin (Q.packingContainer l W).dim) : 1 < (Q.packingContainer l W).length i :=
  one_lt_length_consBinaryList (one_lt_length_difference (Q.consBinaryList l).difference) _ i

lemma dim_packingContainer (Q : GAP G) (l : List G) (W : Finset G) :
    (Q.packingContainer l W).dim = Q.dim + l.length + #W := by
  simp [packingContainer, dim_consBinaryList]

lemma card_packingContainer_le (Q : GAP G) (l : List G) (W : Finset G) :
    #(Q.packingContainer l W).carrier ≤
      2 ^ (#W + 2 * (Q.dim + l.length) + l.length) * Q.boxVolume := by
  refine (card_consBinaryList_le _ _).trans_eq ?_
  rw [length_toList, boxVolume_difference, boxVolume_difference, dim_difference,
    boxVolume_consBinaryList, dim_consBinaryList]
  ring

end GAP

/-- The size bound of the progression containing $X$. Let $m$ be `translateCount κ`. If
$a \le 8 \kappa$, $b \le$ `bohrGAPDim κ`, $n \le m ($`iterationBound κ`$ + 1)$ and
$0 \le y \le \kappa^4 x$, then $2^{a + 2(b + n) + n} y \le e^{E(\kappa)} x$, where $E$ is
`containerExponent`. -/
private lemma two_pow_mul_le_exp_containerExponent_mul {κ x y : ℝ} {a b n : ℕ} (hκ : 2 ≤ κ)
    (ha : (a : ℝ) ≤ 8 * κ) (hb : (b : ℝ) ≤ bohrGAPDim κ)
    (hn : (n : ℝ) ≤ translateCount κ * (iterationBound κ + 1)) (hy₀ : 0 ≤ y)
    (hy : y ≤ κ ^ 4 * x) :
    2 ^ (a + 2 * (b + n) + n) * y ≤ Real.exp (containerExponent κ) * x := by
  have h₂ (n : ℕ) : (2 : ℝ) ^ n ≤ Real.exp n := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ zero_le_two Real.exp_one_gt_two.le n
  have hκ₄ : κ ^ 4 ≤ Real.exp (4 * κ) := by
    simpa [← Real.exp_nat_mul] using
      pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp κ] : κ ≤ Real.exp κ) 4
  have hx : 0 ≤ x := nonneg_of_mul_nonneg_right (hy₀.trans hy) (by positivity)
  refine (mul_le_mul (h₂ _) (hy.trans (mul_le_mul_of_nonneg_right hκ₄ hx)) hy₀
    (Real.exp_nonneg _)).trans ?_
  rw [← mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hx
  push_cast
  linarith [mul_add_two_mul_bohrGAPDim_add_le_containerExponent κ]

/-- Let $X$ be a nonempty finite subset of an abelian group with $|X + X| \le \kappa |X|$. Given a
subset $X_1 \subseteq X$ with $|X| \le 8 |X_1|$ and a proper progression $Q_1 \subseteq 2X - 2X$
with the bounds of `exists_proper_gap_zmod_subset_add_sub_add_card_le`, the set $X$ lies in a
progression with all lengths at least $2$, of dimension at most $E$ and of size at most
$e^{E} |X|$, where $E$ is `containerExponent κ`. The group may be infinite. -/
lemma exists_gap_subset_dim_le_card_le_of_subset_add_sub_add
    {κ : ℝ} {X X₁ : Finset G} {Q₁ : GAP G} (hXne : X.Nonempty) (hκ : 2 ≤ κ)
    (hXX : ((X + X).card : ℝ) ≤ κ * X.card) (hX₁X : X₁ ⊆ X) (hX₁card : X.card ≤ 8 * X₁.card)
    (hQ₁proper : Q₁.Proper) (hQ₁dimle : (Q₁.dim : ℝ) ≤ bohrGAPDim κ)
    (hQ₁subX : Q₁.carrier ⊆ (X + X) - (X + X))
    (hQlow : (X.card : ℝ) ≤ 8 * bohrLoss (bohrGAPDim κ) * Q₁.carrier.card) :
    ∃ P : GAP G,
      X ⊆ P.carrier ∧
        (∀ i, 1 < P.length i) ∧
        ((P.dim : ℝ) ≤ containerExponent κ) ∧
        (P.carrier.card : ℝ) ≤ Real.exp (containerExponent κ) * X.card := by
  obtain ⟨l, F, hl, hlen, hQ₁X, hF, hcover⟩ := exists_length_le_iterationBound_subset_add_sub
    hXne (by linarith) hXX hX₁X Q₁.nonempty hQ₁subX hQlow
  obtain ⟨W, hW, hXW⟩ := exists_card_le_subset_sub_sub_add (by linarith) hXX
    (card_pos.1 (by grind [hXne.card_pos])) hX₁X hX₁card (hcover.trans
      (add_sub_subset_add_sub_add (fun _ hx ↦ mem_listSubsetSum_of_mem (mem_toList.2 hx))
        (zero_mem_listSubsetSum F.toList)))
  obtain ⟨-, hlcard⟩ := forall₂_and.1 hl
  have hlength : ((l.flatMap Finset.toList ++ F.toList).length : ℝ) ≤
      translateCount κ * (iterationBound κ + 1) := by
    rw [List.length_append, length_flatMap_toList hlcard, length_toList]
    push_cast
    linarith [mul_le_mul_of_nonneg_left hlen (Nat.cast_nonneg (α := ℝ) (translateCount κ)),
      (by exact_mod_cast hF : (#F : ℝ) ≤ translateCount κ)]
  refine ⟨Q₁.packingContainer (l.flatMap Finset.toList ++ F.toList) W,
    hXW.trans (GAP.sub_sub_add_subset_packingContainer ?_ W),
    GAP.one_lt_length_packingContainer _ _ _, ?_, ?_⟩
  · rw [listSubsetSum_append, ← add_assoc]
    exact add_subset_add_right (add_subset_add_left (sum_subset_listSubsetSum_flatMap_toList l))
  · rw [GAP.dim_packingContainer]
    push_cast
    linarith [mul_add_bohrGAPDim_add_le_containerExponent hκ]
  · refine (Nat.cast_le.2 (Q₁.card_packingContainer_le _ W)).trans ?_
    rw [GAP.boxVolume, ← Q₁.card_eq_prod_length hQ₁proper]
    push_cast
    exact two_pow_mul_le_exp_containerExponent_mul hκ hW hQ₁dimle hlength (by positivity) hQ₁X

end Packing

/-- Let $q$ be prime and let $X \subseteq \mathbb{Z}/q\mathbb{Z}$ satisfy $|X + X| \le \kappa |X|$
and $|X| \ge 256 d$, where $d$ is `bohrGAPDim κ`. Then $X$ lies in a GAP with all lengths at
least $2$, of dimension at most $E$ and of size at most $e^{E} |X|$, where $E$ is
`containerExponent κ`.

No upper bound on $|X|$ in terms of $q$ is needed, because the Fourier-analytic steps take place in
$\mathbb{Z}/m\mathbb{Z}$ with $m \le \kappa^{16} |X|$. The lemma
`exists_twoProperGAP_dim_le_freimanDim` then bounds the dimension by the Freiman dimension of
$X$. -/
lemma exists_gap_zmod_subset_dim_le_card_le {q : ℕ} {κ : ℝ} (X : Finset (ZMod q))
    (hq : Nat.Prime q) (hκ : 2 ≤ κ)
    (hXX : ((X + X).card : ℝ) ≤ κ * X.card)
    (hXlower : 256 * (bohrGAPDim κ : ℝ) ≤ X.card) :
    ∃ P : GAP (ZMod q),
      X ⊆ P.carrier ∧
        (∀ i, 1 < P.length i) ∧
        ((P.dim : ℝ) ≤ containerExponent κ) ∧
        (P.carrier.card : ℝ) ≤ Real.exp (containerExponent κ) * X.card := by
  obtain ⟨X₁, Q₁, hX₁X, hX₁card, hQ₁proper, hQ₁dimle, hQ₁subX, hQlow⟩ :=
    exists_proper_gap_zmod_subset_add_sub_add_card_le X hq hκ hXX hXlower
  exact exists_gap_subset_dim_le_card_le_of_subset_add_sub_add
    (nonempty_of_mul_bohrGAPDim_le hXlower) hκ hXX hX₁X hX₁card
    hQ₁proper hQ₁dimle hQ₁subX hQlow

end

end ChangFreimanRuzsa
