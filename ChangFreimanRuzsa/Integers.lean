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
generalized arithmetic progression of dimension at most `changContainerExponent (2 * κ)` and of
size at most $e^{C} |X|$, where $C$ is `changIntExponent κ`. This is Chang's form of Freiman's
theorem, Proposition 1.3 of Green and Tao, *Compressions, convex geometry and the Freiman–Bilu
theorem*. The budget `changIntExponent κ` is bounded by a polynomial in $\kappa$.

A progression of $\mathbb{Z}/q\mathbb{Z}$ that contains the reduction of $X$ modulo $q$ need not
come from a progression of $\mathbb{Z}$ that contains $X$, because it may wrap around. So the
statement for $\mathbb{Z}/q\mathbb{Z}$ in `ChangFreimanRuzsa.Cyclic` is not used. Only the first
step of its proof is carried out modulo a large prime $q$. It gives a proper progression inside
$2X - 2X$ in the reduction of $X$ modulo $q$. The reduction is a Freiman isomorphism of order $8$
on $X$, so `exists_transported_gap` carries this progression back to a proper progression of
$\mathbb{Z}$ inside $2X - 2X$. The rest of the argument, the covering of $X$ by translates and the
properization, takes place in $\mathbb{Z}$. These steps are stated for general groups in
`ChangFreimanRuzsa.Container` and `ChangFreimanRuzsa.Cyclic`.

A set too small for this argument is first replaced by its sum with a long arithmetic progression.

## Main definitions

* `changIntExponent κ`: the budget, a polynomially bounded function of the doubling.

## Main statements

* `exists_coarseGAP_container_int`: a set of integers with small doubling that is not too small
  lies in a progression of bounded dimension and size.
* `exists_twoProperGAP_int_of_small_sumset`: Chang's theorem for sets of integers that are not too
  small.
* `exists_twoProperGAP_of_small_sumset`: Chang's theorem for sets of integers.
-/

public section

open Finset
open scoped Pointwise

namespace ChangFreimanRuzsa

/-- The budget of Chang's theorem for sets of integers. -/
@[expose] noncomputable def changIntExponent (κ : ℝ) : ℝ :=
  changZModExponent (2 * κ) + changContainerExponent (2 * κ) + 1

/-! ## Thickening -/

private def spread (M : ℤ) (N : ℕ) : Finset ℤ :=
  (range N).image fun i : ℕ ↦ M * i

private lemma card_spread_le (M : ℤ) (N : ℕ) : #(spread M N) ≤ N :=
  card_image_le.trans_eq (card_range N)

private lemma card_spread {M : ℤ} (hM : M ≠ 0) (N : ℕ) : #(spread M N) = N := by
  rw [spread, card_image_of_injective (f := fun i : ℕ ↦ M * i) _
    ((mul_right_injective₀ hM).comp Nat.cast_injective), card_range]

private lemma spread_add_spread_subset (M : ℤ) (N : ℕ) :
    spread M N + spread M N ⊆ spread M (2 * N) := by
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hz
  obtain ⟨i, hi, rfl⟩ := mem_image.1 ha
  obtain ⟨j, hj, rfl⟩ := mem_image.1 hb
  rw [mem_range] at hi hj
  refine mem_image.2 ⟨i + j, mem_range.2 (by grind), ?_⟩
  push_cast
  ring

private lemma subset_add_spread (X : Finset ℤ) (M : ℤ) {N : ℕ} (hN : 0 < N) :
    X ⊆ X + spread M N :=
  subset_add_left X (mem_image.2 ⟨0, mem_range.2 hN, by simp⟩)

private lemma card_add_spread {X : Finset ℤ} {M : ℤ} (hM : ∀ x ∈ X, ∀ y ∈ X, |x - y| < M)
    (N : ℕ) : #(X + spread M N) = #X * N := by
  rcases X.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  have hM0 : 0 < M := by simpa using hM x₀ hx₀ x₀ hx₀
  rw [card_add_iff.2 ?_, card_spread hM0.ne']
  rintro ⟨x, a⟩ hxa ⟨y, b⟩ hyb h
  obtain ⟨hx, ha⟩ := Set.mem_prod.1 hxa
  obtain ⟨hy, hb⟩ := Set.mem_prod.1 hyb
  obtain ⟨i, -, rfl⟩ := mem_image.1 (mem_coe.1 ha)
  obtain ⟨j, -, rfl⟩ := mem_image.1 (mem_coe.1 hb)
  dsimp only at h
  have hxy : x - y = 0 :=
    Int.eq_zero_of_abs_lt_dvd ⟨j - i, by linear_combination h⟩ (hM x hx y hy)
  exact Prod.ext (by linarith) (by linarith)

private lemma card_add_spread_add_le (X : Finset ℤ) (M : ℤ) (N : ℕ) :
    #((X + spread M N) + (X + spread M N)) ≤ #(X + X) * (2 * N) := by
  rw [add_add_add_comm]
  exact card_add_le.trans (Nat.mul_le_mul_left _
    ((card_le_card (spread_add_spread_subset M N)).trans (card_spread_le M _)))

private lemma lt_mul_floor_add_one {E : ℝ} {n : ℕ} (hn : 0 < n) (hE : 1 ≤ E) :
    E < ((n * (⌊E / n⌋₊ + 1) : ℕ) : ℝ) ∧ ((n * (⌊E / n⌋₊ + 1) : ℕ) : ℝ) ≤ 2 * E * n := by
  have hn' : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hn
  push_cast
  constructor <;> nlinarith [Nat.lt_floor_add_one (E / n),
    Nat.floor_le (div_nonneg (by linarith) (by linarith) : 0 ≤ E / n),
    div_mul_cancel₀ E (by positivity : (n : ℝ) ≠ 0)]

private lemma exists_thickening {κ E : ℝ} {X : Finset ℤ} (hX : X.Nonempty)
    (hXX : (#(X + X) : ℝ) ≤ κ * #X) (hE : 1 ≤ E) :
    ∃ X' : Finset ℤ, X ⊆ X' ∧ (#(X' + X') : ℝ) ≤ 2 * κ * #X' ∧ E < #X' ∧
      (#X' : ℝ) ≤ 2 * E * #X := by
  set M : ℤ := ((X - X).sup Int.natAbs : ℕ) + 1
  have hM : ∀ x ∈ X, ∀ y ∈ X, |x - y| < M := by
    intro x hx y hy
    have := le_sup (f := Int.natAbs) (sub_mem_sub hx hy)
    rw [Int.abs_eq_natAbs]
    grind
  obtain ⟨hlt, hle⟩ := lt_mul_floor_add_one hX.card_pos hE
  set N : ℕ := ⌊E / #X⌋₊ + 1
  have hcard : #(X + spread M N) = #X * N := card_add_spread hM N
  refine ⟨X + spread M N, subset_add_spread X M (by grind), ?_, by rwa [hcard],
    by rwa [hcard]⟩
  calc (#((X + spread M N) + (X + spread M N)) : ℝ)
    _ ≤ ((#(X + X) * (2 * N) : ℕ) : ℝ) := mod_cast card_add_spread_add_le X M N
    _ = #(X + X) * (2 * N) := by push_cast; ring
    _ ≤ κ * #X * (2 * N) := by gcongr
    _ = 2 * κ * #(X + spread M N) := by rw [hcard]; push_cast; ring

/-! ## Reduction modulo a large prime -/

private lemma exists_prime_gt (X : Finset ℤ) :
    ∃ (q : ℕ) (M : ℤ), q.Prime ∧ 16 * M < q ∧ ∀ x ∈ X, |x| ≤ M := by
  obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes (16 * X.sup Int.natAbs + 1)
  refine ⟨q, (X.sup Int.natAbs : ℕ), hprime, by grind, ?_⟩
  intro x hx
  rw [Int.abs_eq_natAbs]
  exact mod_cast le_sup (f := Int.natAbs) hx

private lemma abs_sum_le_card_mul {X : Finset ℤ} {M : ℤ} (hX : ∀ x ∈ X, |x| ≤ M)
    {s : Multiset ℤ} (hs : ∀ x ∈ s, x ∈ X) : |s.sum| ≤ Multiset.card s * M := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.sum_cons, Multiset.card_cons]
    push_cast
    linarith [abs_add_le a s.sum, hX a (hs a (Multiset.mem_cons_self a s)),
      ih fun x hx ↦ hs x (Multiset.mem_cons_of_mem hx)]

private lemma intCast_inj_of_abs_sub_lt {q : ℕ} {a b : ℤ} (h : |b - a| < q) :
    (a : ZMod q) = b ↔ a = b :=
  ⟨fun hab ↦ (sub_eq_zero.1 (Int.eq_zero_of_abs_lt_dvd
    ((ZMod.intCast_eq_intCast_iff_dvd_sub a b q).1 hab) h)).symm, fun hab ↦ by rw [hab]⟩

/-- Reduction modulo $q$ is a Freiman isomorphism of order $8$ on a set of integers of absolute
value less than $q / 16$. -/
private lemma isAddFreimanIso_intCast {q : ℕ} {M : ℤ} {X : Finset ℤ} (hq : 16 * M < q)
    (hX : ∀ x ∈ X, |x| ≤ M) :
    IsAddFreimanIso 8 (X : Set ℤ) (X.image (Int.cast : ℤ → ZMod q) : Set (ZMod q)) Int.cast where
  bijOn := by
    rw [coe_image]
    refine Set.InjOn.bijOn_image ?_
    intro x hx y hy h
    refine (intCast_inj_of_abs_sub_lt ?_).1 h
    linarith [abs_sub y x, hX x hx, hX y hy, abs_nonneg x]
  map_sum_eq_map_sum s t hs ht hs' ht' := by
    have h₁ := abs_sum_le_card_mul hX fun x hx ↦ mem_coe.1 (hs hx)
    have h₂ := abs_sum_le_card_mul hX fun x hx ↦ mem_coe.1 (ht hx)
    rw [hs'] at h₁
    rw [ht'] at h₂
    rw [← Int.cast_multiset_sum, ← Int.cast_multiset_sum]
    refine intCast_inj_of_abs_sub_lt ?_
    push_cast at h₁ h₂
    linarith [abs_sub t.sum s.sum]

private lemma card_image_intCast_add_le (q : ℕ) (X : Finset ℤ) :
    #(X.image (Int.cast : ℤ → ZMod q) + X.image (Int.cast : ℤ → ZMod q)) ≤ #(X + X) := by
  have h := image_add (Int.castAddHom (ZMod q)) (s := X) (t := X)
  simp only [Int.coe_castAddHom] at h
  rw [← h]
  exact card_image_le

/-! ## The progression inside `2X - 2X` -/

/-- Let $c_\kappa$ be `changContainerExponent κ` and $d_\kappa$ be `changGapDim κ`. A finite set
$X \subseteq \mathbb{Z}$ with $|X + X| \le \kappa |X|$ and $e^{c_\kappa} < |X|$ has a subset $X_1$
with $|X| \le 8 |X_1|$ and a proper progression $Q_1 \subseteq 2X - 2X$ of dimension at most
$d_\kappa$ with $|X| \le 8 \cdot 2^{12 d_\kappa^2} |Q_1|$.

The progression is the one that `exists_model_gap` gives for the reduction of `X` modulo a large
prime, carried back to `ℤ` by `exists_transported_gap`. -/
private lemma exists_model_gap_int {κ : ℝ} (X : Finset ℤ) (hκ : 2 ≤ κ)
    (hXX : (#(X + X) : ℝ) ≤ κ * #X) (hXlower : Real.exp (changContainerExponent κ) < #X) :
    ∃ (X₁ : Finset ℤ) (Q₁ : GAP ℤ), X₁ ⊆ X ∧ #X ≤ 8 * #X₁ ∧ Q₁.Proper ∧
      (Q₁.dim : ℝ) ≤ changGapDim κ ∧ Q₁.carrier ⊆ (X + X) - (X + X) ∧
      (#X : ℝ) ≤ 8 * 2 ^ (12 * changGapDim κ ^ 2) * #Q₁.carrier := by
  obtain ⟨q, M, hq, hM, hXM⟩ := exists_prime_gt X
  have hiso := isAddFreimanIso_intCast hM hXM
  have hcard : #(X.image (Int.cast : ℤ → ZMod q)) = #X := card_image_of_injOn hiso.bijOn.injOn
  obtain ⟨Y₁, Q, hY₁, hY₁card, hQ, hQdim, hQsub, hQcard⟩ :=
    exists_model_gap (X.image (Int.cast : ℤ → ZMod q)) hq hκ
      ((Nat.cast_le.2 (card_image_intCast_add_le q X)).trans (hcard ▸ hXX)) (by rwa [hcard])
  obtain ⟨Q₁, hQ₁, hQ₁dim, hQ₁card, hQ₁sub⟩ := exists_transported_gap hiso Q hQ hQsub
  have hY : Y₁ ⊆ (X.filter fun x : ℤ ↦ (x : ZMod q) ∈ Y₁).image Int.cast := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.1 (hY₁ hy)
    exact mem_image_of_mem _ (mem_filter.2 ⟨hx, hy⟩)
  rw [hcard] at hY₁card hQcard
  exact ⟨X.filter fun x : ℤ ↦ (x : ZMod q) ∈ Y₁, Q₁, filter_subset _ _,
    hY₁card.trans (Nat.mul_le_mul_left 8 ((card_le_card hY).trans card_image_le)), hQ₁,
    by rwa [hQ₁dim], hQ₁sub, by rwa [hQ₁card]⟩

/-- Let $c_\kappa$ be `changContainerExponent κ`. A finite set $X \subseteq \mathbb{Z}$ with
$|X + X| \le \kappa |X|$ and $e^{c_\kappa} < |X|$ lies in a generalized arithmetic progression of
dimension at most $c_\kappa$ and of size at most $e^{c_\kappa} |X|$. -/
lemma exists_coarseGAP_container_int {κ : ℝ} (X : Finset ℤ) (hκ : 2 ≤ κ)
    (hXX : (#(X + X) : ℝ) ≤ κ * #X) (hXlower : Real.exp (changContainerExponent κ) < #X) :
    ∃ P : GAP ℤ, X ⊆ P.carrier ∧ (∀ i, 1 < P.length i) ∧
      (P.dim : ℝ) ≤ changContainerExponent κ ∧
      (#P.carrier : ℝ) ≤ Real.exp (changContainerExponent κ) * #X := by
  obtain ⟨X₁, Q₁, hX₁X, hX₁card, hQ₁, hQ₁dim, hQ₁sub, hQ₁card⟩ :=
    exists_model_gap_int X hκ hXX hXlower
  exact exists_coarseGAP_container_of_model_gap
    (card_pos.1 (mod_cast (Real.exp_pos _).trans hXlower)) hκ hXX hX₁X hX₁card hQ₁ hQ₁dim hQ₁sub
    hQ₁card

/-! ## Chang's theorem -/

/-- **Chang's theorem** for sets of integers that are not too small. Write $c_\kappa$ for
`changContainerExponent κ` and $C_\kappa$ for `changZModExponent κ`. A finite set
$X \subseteq \mathbb{Z}$ with $|X + X| \le \kappa |X|$ and $e^{c_\kappa} < |X|$ is contained in a
$2$-proper generalized arithmetic progression of dimension at most $c_\kappa$ and of size at most
$e^{C_\kappa} |X|$. -/
theorem exists_twoProperGAP_int_of_small_sumset {κ : ℝ} (X : Finset ℤ) (hκ : 2 ≤ κ)
    (hXX : (#(X + X) : ℝ) ≤ κ * #X) (hXlower : Real.exp (changContainerExponent κ) < #X) :
    ∃ Q : GAP ℤ, Q.TwoProper ∧ X ⊆ Q.carrier ∧ (∀ i, 1 < Q.length i) ∧
      (Q.dim : ℝ) ≤ changContainerExponent κ ∧
      (#Q.carrier : ℝ) ≤ Real.exp (changZModExponent κ) * #X := by
  obtain ⟨P, hXP, -, hPdim, hPcard⟩ := exists_coarseGAP_container_int X hκ hXX hXlower
  exact exists_twoProperGAP_of_coarseGAP
    (fun _ ↦ GAP.injOn_nsmul_of_isAddTorsionFree _) hXP hPdim hPcard (Nat.le_ceil _)

private lemma exp_mul_le_exp_add_add_one_mul {z c x y : ℝ} (hx : 0 ≤ x)
    (hyx : y ≤ 2 * Real.exp c * x) : Real.exp z * y ≤ Real.exp (z + c + 1) * x := by
  rw [Real.exp_add, Real.exp_add]
  refine (mul_le_mul_of_nonneg_left hyx (Real.exp_nonneg z)).trans ?_
  nlinarith [Real.add_one_le_exp (1 : ℝ),
    mul_nonneg (mul_nonneg (Real.exp_nonneg z) (Real.exp_nonneg c)) hx]

/-- **Chang's theorem** for sets of integers. A finite nonempty set $X \subseteq \mathbb{Z}$ with
$|X + X| \le \kappa |X|$ is contained in a $2$-proper generalized arithmetic progression of
dimension at most `changContainerExponent (2 * κ)` and of size at most $e^{C} |X|$, where $C$ is
`changIntExponent κ`. -/
theorem exists_twoProperGAP_of_small_sumset {κ : ℝ} (X : Finset ℤ) (hX : X.Nonempty)
    (hκ : 2 ≤ κ) (hXX : (#(X + X) : ℝ) ≤ κ * #X) :
    ∃ P : GAP ℤ, P.TwoProper ∧ X ⊆ P.carrier ∧
      (P.dim : ℝ) ≤ changContainerExponent (2 * κ) ∧
      (#P.carrier : ℝ) ≤ Real.exp (changIntExponent κ) * #X := by
  have hκ' : (2 : ℝ) ≤ 2 * κ := by linarith
  obtain ⟨X', hXX', hX'X', hX'lower, hX'upper⟩ :=
    exists_thickening hX hXX (Real.one_le_exp (changContainerExponent_pos hκ').le)
  obtain ⟨P, hP, hX'P, -, hdim, hcard⟩ :=
    exists_twoProperGAP_int_of_small_sumset X' hκ' hX'X' hX'lower
  exact ⟨P, hP, hXX'.trans hX'P, hdim,
    hcard.trans (exp_mul_le_exp_add_add_one_mul (Nat.cast_nonneg _) hX'upper)⟩

end ChangFreimanRuzsa
