/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.Cyclic
import ChangFreimanRuzsa.FreimanRigidity

/-!
# Chang's theorem for sets of integers

A finite set $X \subseteq \mathbb{Z}$ with $|X + X| \le \kappa |X|$ lies in a $2$-proper
generalized arithmetic progression of dimension at most `containerExponent (2 * κ)` and of
size at most $e^{C} |X|$, where $C$ is `intExponent κ`. This is Chang's form of Freiman's
theorem, Proposition 1.3 of Green and Tao, *Compressions, convex geometry and the Freiman–Bilu
theorem*. The exponent `intExponent κ` is bounded by a polynomial in $\kappa$.

A progression of $\mathbb{Z}/q\mathbb{Z}$ that contains the reduction of $X$ modulo $q$ need not
come from a progression of $\mathbb{Z}$ that contains $X$, because it may wrap around. So the
statement for $\mathbb{Z}/q\mathbb{Z}$ in `ChangFreimanRuzsa.Cyclic` is not used. Only the first
step of its proof is carried out modulo a large prime $q$. It gives a proper progression inside
$2X - 2X$ in the reduction of $X$ modulo $q$. The reduction is a Freiman isomorphism of order $8$
on $X$, so `exists_proper_gap_subset_add_sub_add_of_isAddFreimanIso` carries this progression back
to a proper progression of $\mathbb{Z}$ inside $2X - 2X$. The rest of the argument, the covering of
$X$ by translates and the passage to a $2$-proper progression, takes place in $\mathbb{Z}$. These
steps are stated for general groups in `ChangFreimanRuzsa.Container` and `ChangFreimanRuzsa.Cyclic`.

A set too small for this argument is first replaced by its sum with a long arithmetic progression
$\{0, M, \dots, (N - 1) M\}$.

## Main definitions

* `intExponent κ`: the exponent of the bound for the size of the progression, a polynomially
  bounded function of the doubling.

## Main statements

* `exists_gap_int_subset_dim_le_card_le`: a set of integers with small doubling that is not too
  small lies in a progression of bounded dimension and size.
* `exists_twoProperGAP_int_of_small_sumset`: Chang's theorem for sets of integers that are not too
  small.
* `exists_twoProperGAP_of_small_sumset`: Chang's theorem for sets of integers.
-/

public section

open Finset
open scoped Pointwise

namespace ChangFreimanRuzsa

/-- The exponent of the bound for the size of the progression in Chang's theorem for sets of
integers. -/
@[expose] noncomputable def intExponent (κ : ℝ) : ℝ :=
  zmodExponent (2 * κ) + containerExponent (2 * κ) + 1

private lemma abs_le_sup_natAbs {X : Finset ℤ} {x : ℤ} (hx : x ∈ X) : |x| ≤ X.sup Int.natAbs := by
  rw [Int.abs_eq_natAbs]
  exact mod_cast le_sup hx

/-! ## Enlarging a small set -/

private lemma image_nsmul_range_add_subset (M : ℤ) (N : ℕ) :
    (range N).image (· • M) + (range N).image (· • M) ⊆ (range (2 * N)).image (· • M) := by
  intro z hz
  simp only [mem_add, mem_image, mem_range] at hz ⊢
  obtain ⟨_, ⟨i, hi, rfl⟩, _, ⟨j, hj, rfl⟩, rfl⟩ := hz
  exact ⟨i + j, by grind, add_nsmul M i j⟩

private lemma card_add_add_image_nsmul_range_le (X : Finset ℤ) (M : ℤ) (N : ℕ) :
    #((X + X) + ((range N).image (· • M) + (range N).image (· • M))) ≤ #(X + X) * (2 * N) :=
  card_add_le.trans (Nat.mul_le_mul_left _ ((card_le_card (image_nsmul_range_add_subset M N)).trans
    (card_image_le.trans_eq (card_range _))))

/-- If $M$ exceeds the diameter of $X$, then the sum of $X$ and $\{0, M, \dots, (N - 1) M\}$ has
$|X| N$ elements. -/
private lemma card_add_image_nsmul_range {X : Finset ℤ} {M : ℤ}
    (hM : ∀ x ∈ X, ∀ y ∈ X, |x - y| < M) (N : ℕ) : #(X + (range N).image (· • M)) = #X * N := by
  rcases X.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  have hM0 : M ≠ 0 := (by simpa using hM x₀ hx₀ x₀ hx₀ : 0 < M).ne'
  rw [card_add_iff.2 ?_, card_image_of_injective _ fun i j h ↦ by simpa [hM0] using h, card_range]
  rintro ⟨x, a⟩ ⟨hx, ha⟩ ⟨y, b⟩ ⟨hy, hb⟩ h
  obtain ⟨i, -, rfl⟩ := mem_image.1 (mem_coe.1 ha)
  obtain ⟨j, -, rfl⟩ := mem_image.1 (mem_coe.1 hb)
  simp only [nsmul_eq_mul] at h
  obtain rfl : x = y :=
    sub_eq_zero.1 <| Int.eq_zero_of_abs_lt_dvd ⟨j - i, by linear_combination h⟩ (hM x hx y hy)
  simp_all

private lemma lt_mul_floor_add_one {E : ℝ} {n : ℕ} (hn : 0 < n) (hE : 1 ≤ E) :
    E < ((n * (⌊E / n⌋₊ + 1) : ℕ) : ℝ) ∧ ((n * (⌊E / n⌋₊ + 1) : ℕ) : ℝ) ≤ 2 * E * n := by
  push_cast
  constructor <;> nlinarith [Nat.lt_floor_add_one (E / n), (Nat.one_le_cast.2 hn : (1 : ℝ) ≤ n),
    Nat.floor_le (div_nonneg (by linarith) (by linarith) : 0 ≤ E / n),
    div_mul_cancel₀ E (by positivity : (n : ℝ) ≠ 0)]

/-- A nonempty set $X$ with $|X + X| \le \kappa |X|$ lies in a set $X'$ with
$|X' + X'| \le 2 \kappa |X'|$ and $E < |X'| \le 2 E |X|$, namely the sum of $X$ and an arithmetic
progression whose common difference exceeds the diameter of $X$. -/
private lemma exists_large_superset_of_card_add_le {κ E : ℝ} {X : Finset ℤ} (hX : X.Nonempty)
    (hXX : (#(X + X) : ℝ) ≤ κ * #X) (hE : 1 ≤ E) :
    ∃ X' : Finset ℤ, X ⊆ X' ∧ (#(X' + X') : ℝ) ≤ 2 * κ * #X' ∧ E < #X' ∧
      (#X' : ℝ) ≤ 2 * E * #X := by
  set M : ℤ := (X - X).sup Int.natAbs + 1
  set N : ℕ := ⌊E / #X⌋₊ + 1
  have hcard : #(X + (range N).image (· • M)) = #X * N :=
    card_add_image_nsmul_range (fun x hx y hy ↦
      (abs_le_sup_natAbs (sub_mem_sub hx hy)).trans_lt (by grind)) N
  obtain ⟨hlt, hle⟩ := lt_mul_floor_add_one hX.card_pos hE
  refine ⟨X + (range N).image (· • M), subset_add_left X (mem_image.2 ⟨0, by simp [N], by simp⟩),
    ?_, by rwa [hcard], by rwa [hcard]⟩
  rw [add_add_add_comm]
  calc (#((X + X) + ((range N).image (· • M) + (range N).image (· • M))) : ℝ)
    _ ≤ ((#(X + X) * (2 * N) : ℕ) : ℝ) := mod_cast card_add_add_image_nsmul_range_le X M N
    _ ≤ κ * #X * (2 * N) := by push_cast; gcongr
    _ = 2 * κ * #(X + (range N).image (· • M)) := by rw [hcard]; push_cast; ring

/-! ## Reduction modulo a large prime -/

private lemma abs_sum_le_card_nsmul {X : Finset ℤ} {s : Multiset ℤ} (hs : ∀ x ∈ s, x ∈ X) :
    |s.sum| ≤ Multiset.card s • ((X.sup Int.natAbs : ℕ) : ℤ) := by
  refine Multiset.abs_sum_le_sum_abs.trans ?_
  simpa using (s.map abs).sum_le_card_nsmul _
    (by simpa using fun x hx ↦ abs_le_sup_natAbs (hs x hx))

private lemma intCast_inj_of_abs_sub_lt {q : ℕ} {a b : ℤ} (h : |b - a| < q) :
    (a : ZMod q) = b ↔ a = b :=
  ⟨fun hab ↦ (sub_eq_zero.1 (Int.eq_zero_of_abs_lt_dvd
    ((ZMod.intCast_eq_intCast_iff_dvd_sub a b q).1 hab) h)).symm, fun hab ↦ by rw [hab]⟩

/-- Reduction modulo $q$ is a Freiman isomorphism of order $8$ on a set of integers of absolute
value less than $q / 16$. -/
private lemma isAddFreimanIso_intCast {q : ℕ} {X : Finset ℤ} (hq : 16 * X.sup Int.natAbs < q) :
    IsAddFreimanIso 8 (X : Set ℤ) (X.image (Int.cast : ℤ → ZMod q) : Set (ZMod q)) Int.cast where
  bijOn := by
    rw [coe_image]
    refine Set.InjOn.bijOn_image ?_
    intro x hx y hy h
    refine (intCast_inj_of_abs_sub_lt ?_).1 h
    linarith [abs_sub y x, abs_le_sup_natAbs hx, abs_le_sup_natAbs hy,
      (by exact_mod_cast hq : 16 * ((X.sup Int.natAbs : ℕ) : ℤ) < q), abs_nonneg x]
  map_sum_eq_map_sum s t hs ht hs' ht' := by
    rw [← Int.cast_multiset_sum, ← Int.cast_multiset_sum]
    refine intCast_inj_of_abs_sub_lt ?_
    linarith [abs_sub t.sum s.sum, (by exact_mod_cast hq : 16 * ((X.sup Int.natAbs : ℕ) : ℤ) < q),
      (by simpa [hs'] using abs_sum_le_card_nsmul (X := X) fun x hx ↦ mem_coe.1 (hs hx) :
        |s.sum| ≤ 8 * X.sup Int.natAbs),
      (by simpa [ht'] using abs_sum_le_card_nsmul (X := X) fun x hx ↦ mem_coe.1 (ht hx) :
        |t.sum| ≤ 8 * X.sup Int.natAbs)]

private lemma card_image_intCast_add_le (q : ℕ) (X : Finset ℤ) :
    #(X.image (Int.cast : ℤ → ZMod q) + X.image (Int.cast : ℤ → ZMod q)) ≤ #(X + X) := by
  have h := image_add (Int.castAddHom (ZMod q)) (s := X) (t := X)
  simp only [Int.coe_castAddHom] at h
  rw [← h]
  exact card_image_le

/-! ## The progression inside `2X - 2X` -/

/-- Let $c_\kappa$ be `containerExponent κ` and $d_\kappa$ be `bohrGAPDim κ`. A finite set
$X \subseteq \mathbb{Z}$ with $|X + X| \le \kappa |X|$ and $e^{c_\kappa} < |X|$ has a subset $X_1$
with $|X| \le 8 |X_1|$ and a proper progression $Q_1 \subseteq 2X - 2X$ of dimension at most
$d_\kappa$ with $|X| \le 8 \cdot 2^{12 d_\kappa^2} |Q_1|$.

The progression is the one that `exists_proper_gap_zmod_subset_add_sub_add_card_le` gives for the
reduction of `X` modulo a large prime, carried back to `ℤ` by
`exists_proper_gap_subset_add_sub_add_of_isAddFreimanIso`. -/
private lemma exists_proper_gap_int_subset_add_sub_add_card_le {κ : ℝ} (X : Finset ℤ)
    (hκ : 2 ≤ κ) (hXX : (#(X + X) : ℝ) ≤ κ * #X)
    (hXlower : Real.exp (containerExponent κ) < #X) :
    ∃ (X₁ : Finset ℤ) (Q₁ : GAP ℤ), X₁ ⊆ X ∧ #X ≤ 8 * #X₁ ∧ Q₁.Proper ∧
      (Q₁.dim : ℝ) ≤ bohrGAPDim κ ∧ Q₁.carrier ⊆ (X + X) - (X + X) ∧
      (#X : ℝ) ≤ 8 * 2 ^ (12 * bohrGAPDim κ ^ 2) * #Q₁.carrier := by
  obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes (16 * X.sup Int.natAbs + 1)
  have hiso := isAddFreimanIso_intCast (q := q) (X := X) (by grind)
  have hcard : #(X.image (Int.cast : ℤ → ZMod q)) = #X := card_image_of_injOn hiso.bijOn.injOn
  obtain ⟨Y₁, Q, hY₁, hY₁card, hQ, hQdim, hQsub, hQcard⟩ :=
    exists_proper_gap_zmod_subset_add_sub_add_card_le (X.image (Int.cast : ℤ → ZMod q)) hprime
      hκ ((Nat.cast_le.2 (card_image_intCast_add_le q X)).trans (hcard ▸ hXX)) (by rwa [hcard])
  obtain ⟨Q₁, hQ₁, hQ₁dim, hQ₁card, hQ₁sub⟩ :=
    exists_proper_gap_subset_add_sub_add_of_isAddFreimanIso hiso hQ hQsub
  obtain ⟨X₁, hX₁, rfl⟩ := subset_image_iff.1 hY₁
  rw [hcard] at hY₁card hQcard
  exact ⟨X₁, Q₁, hX₁, hY₁card.trans (Nat.mul_le_mul_left 8 card_image_le), hQ₁, by rwa [hQ₁dim],
    hQ₁sub, by rwa [hQ₁card]⟩

/-- Let $c_\kappa$ be `containerExponent κ`. A finite set $X \subseteq \mathbb{Z}$ with
$|X + X| \le \kappa |X|$ and $e^{c_\kappa} < |X|$ lies in a generalized arithmetic progression of
dimension at most $c_\kappa$ and of size at most $e^{c_\kappa} |X|$. -/
lemma exists_gap_int_subset_dim_le_card_le {κ : ℝ} (X : Finset ℤ) (hκ : 2 ≤ κ)
    (hXX : (#(X + X) : ℝ) ≤ κ * #X) (hXlower : Real.exp (containerExponent κ) < #X) :
    ∃ P : GAP ℤ, X ⊆ P.carrier ∧ (∀ i, 1 < P.length i) ∧
      (P.dim : ℝ) ≤ containerExponent κ ∧
      (#P.carrier : ℝ) ≤ Real.exp (containerExponent κ) * #X := by
  obtain ⟨X₁, Q₁, hX₁X, hX₁card, hQ₁, hQ₁dim, hQ₁sub, hQ₁card⟩ :=
    exists_proper_gap_int_subset_add_sub_add_card_le X hκ hXX hXlower
  exact exists_gap_subset_dim_le_card_le_of_subset_add_sub_add
    (card_pos.1 (mod_cast (Real.exp_pos _).trans hXlower)) hκ hXX hX₁X hX₁card hQ₁ hQ₁dim hQ₁sub
    hQ₁card

/-! ## Chang's theorem -/

/-- **Chang's theorem** for sets of integers that are not too small. Write $c_\kappa$ for
`containerExponent κ` and $C_\kappa$ for `zmodExponent κ`. A finite set
$X \subseteq \mathbb{Z}$ with $|X + X| \le \kappa |X|$ and $e^{c_\kappa} < |X|$ is contained in a
$2$-proper generalized arithmetic progression of dimension at most $c_\kappa$ and of size at most
$e^{C_\kappa} |X|$. -/
theorem exists_twoProperGAP_int_of_small_sumset {κ : ℝ} (X : Finset ℤ) (hκ : 2 ≤ κ)
    (hXX : (#(X + X) : ℝ) ≤ κ * #X) (hXlower : Real.exp (containerExponent κ) < #X) :
    ∃ Q : GAP ℤ, Q.TwoProper ∧ X ⊆ Q.carrier ∧ (∀ i, 1 < Q.length i) ∧
      (Q.dim : ℝ) ≤ containerExponent κ ∧
      (#Q.carrier : ℝ) ≤ Real.exp (zmodExponent κ) * #X := by
  obtain ⟨P, hXP, -, hPdim, hPcard⟩ := exists_gap_int_subset_dim_le_card_le X hκ hXX hXlower
  exact exists_twoProperGAP_subset_dim_le_card_le_of_subset_gap
    (fun _ ↦ GAP.injOn_nsmul_of_isAddTorsionFree _) hXP hPdim hPcard (Nat.le_ceil _)

private lemma exp_mul_le_exp_add_add_one_mul {z c x y : ℝ} (hx : 0 ≤ x)
    (hyx : y ≤ 2 * Real.exp c * x) : Real.exp z * y ≤ Real.exp (z + c + 1) * x := by
  rw [Real.exp_add, Real.exp_add]
  refine (mul_le_mul_of_nonneg_left hyx (Real.exp_nonneg z)).trans ?_
  nlinarith [Real.add_one_le_exp (1 : ℝ),
    mul_nonneg (mul_nonneg (Real.exp_nonneg z) (Real.exp_nonneg c)) hx]

/-- **Chang's theorem** for sets of integers. A finite nonempty set $X \subseteq \mathbb{Z}$ with
$|X + X| \le \kappa |X|$ is contained in a $2$-proper generalized arithmetic progression of
dimension at most `containerExponent (2 * κ)` and of size at most $e^{C} |X|$, where $C$ is
`intExponent κ`. -/
theorem exists_twoProperGAP_of_small_sumset {κ : ℝ} (X : Finset ℤ) (hX : X.Nonempty)
    (hκ : 2 ≤ κ) (hXX : (#(X + X) : ℝ) ≤ κ * #X) :
    ∃ P : GAP ℤ, P.TwoProper ∧ X ⊆ P.carrier ∧
      (P.dim : ℝ) ≤ containerExponent (2 * κ) ∧
      (#P.carrier : ℝ) ≤ Real.exp (intExponent κ) * #X := by
  have hκ' : (2 : ℝ) ≤ 2 * κ := by linarith
  obtain ⟨X', hXX', hX'X', hX'lower, hX'upper⟩ :=
    exists_large_superset_of_card_add_le hX hXX (Real.one_le_exp (containerExponent_pos hκ').le)
  obtain ⟨P, hP, hX'P, -, hdim, hcard⟩ :=
    exists_twoProperGAP_int_of_small_sumset X' hκ' hX'X' hX'lower
  exact ⟨P, hP, hXX'.trans hX'P, hdim,
    hcard.trans (exp_mul_le_exp_add_add_one_mul (Nat.cast_nonneg _) hX'upper)⟩

end ChangFreimanRuzsa
