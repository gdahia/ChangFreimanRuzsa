/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.Cyclic

/-!
# Chang's theorem for sets of integers

A finite set of integers with small doubling lies in a `2`-proper generalized arithmetic
progression of comparable size. This is Chang's form of Freiman's theorem, as in Green and Tao,
*Compressions, convex geometry and the Freiman–Bilu theorem*, Proposition 1.3, with a weaker but
still polynomial budget.

It is deduced from the statement for subsets of `ZMod q` in `Cyclic.lean`: a set too small for
that statement is first replaced by its sum with a long progression, the result is reduced modulo
a large prime, and the progression found in `ZMod q` is lifted to `ℤ` with `q` as an additional
step.

## Main definitions

* `changIntExponent κ`: the budget, a polynomially bounded function of the doubling.

## Main statements

* `exists_twoProperGAP_of_small_sumset`: Chang's theorem for sets of integers.
-/

public section

open Finset
open scoped Pointwise

namespace ChangFreimanRuzsa

/-- The budget of Chang's theorem for sets of integers. -/
@[expose] noncomputable def changIntExponent (κ : ℝ) : ℝ :=
  2 * properizationConstant * (changContainerExponent (2 * κ) + 2) ^ 4 +
    4 * changContainerExponent (2 * κ) + 3

/-! ## Thickening -/

private def spread (M : ℤ) (N : ℕ) : Finset ℤ :=
  (range N).image fun i : ℕ ↦ M * i

private lemma card_spread_le (M : ℤ) (N : ℕ) : #(spread M N) ≤ N :=
  card_image_le.trans_eq (card_range N)

private lemma card_spread {M : ℤ} (hM : M ≠ 0) (N : ℕ) : #(spread M N) = N := by
  have hinj : Function.Injective fun i : ℕ ↦ M * i := fun i j h ↦ by
    exact_mod_cast mul_left_cancel₀ hM h
  rw [spread, card_image_of_injective _ hinj, card_range]

private lemma spread_add_spread_subset (M : ℤ) (N : ℕ) :
    spread M N + spread M N ⊆ spread M (2 * N) := by
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hz
  obtain ⟨i, hi, rfl⟩ := mem_image.1 ha
  obtain ⟨j, hj, rfl⟩ := mem_image.1 hb
  rw [mem_range] at hi hj
  exact mem_image.2 ⟨i + j, mem_range.2 (by omega), by push_cast; ring⟩

private lemma subset_add_spread (X : Finset ℤ) (M : ℤ) {N : ℕ} (hN : 0 < N) :
    X ⊆ X + spread M N := fun x hx ↦ by
  have h0 : (0 : ℤ) ∈ spread M N := mem_image.2 ⟨0, mem_range.2 hN, by simp⟩
  simpa using add_mem_add hx h0

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
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h₁ := Nat.lt_floor_add_one (E / n)
  have h₂ := Nat.floor_le (div_nonneg (by linarith) (by linarith) : 0 ≤ E / n)
  have h₃ : E / n * n = E := div_mul_cancel₀ _ (by positivity)
  push_cast
  constructor <;> nlinarith

private lemma exists_thickening {κ E : ℝ} {X : Finset ℤ} (hX : X.Nonempty)
    (hXX : (#(X + X) : ℝ) ≤ κ * #X) (hE : 1 ≤ E) :
    ∃ X' : Finset ℤ, X ⊆ X' ∧ (#(X' + X') : ℝ) ≤ 2 * κ * #X' ∧ E < #X' ∧
      (#X' : ℝ) ≤ 2 * E * #X := by
  set M : ℤ := ((X - X).sup Int.natAbs : ℕ) + 1
  have hM : ∀ x ∈ X, ∀ y ∈ X, |x - y| < M := fun x hx y hy ↦ by
    have := le_sup (f := Int.natAbs) (sub_mem_sub hx hy)
    rw [Int.abs_eq_natAbs]
    omega
  obtain ⟨hlt, hle⟩ := lt_mul_floor_add_one hX.card_pos hE
  set N : ℕ := ⌊E / #X⌋₊ + 1
  have hcard : #(X + spread M N) = #X * N := card_add_spread hM N
  refine ⟨X + spread M N, subset_add_spread X M (by omega), ?_, by rwa [hcard],
    by rwa [hcard]⟩
  calc (#((X + spread M N) + (X + spread M N)) : ℝ)
    _ ≤ ((#(X + X) * (2 * N) : ℕ) : ℝ) := mod_cast card_add_spread_add_le X M N
    _ = #(X + X) * (2 * N) := by push_cast; ring
    _ ≤ κ * #X * (2 * N) := by gcongr
    _ = 2 * κ * #(X + spread M N) := by rw [hcard]; push_cast; ring

/-! ## Reduction modulo a large prime -/

private lemma exists_prime_ge (X : Finset ℤ) (B : ℝ) :
    ∃ q : ℕ, q.Prime ∧ B ≤ q ∧ ∀ x ∈ X, 2 * |x| < q := by
  obtain ⟨q, hq, hprime⟩ :=
    Nat.exists_infinite_primes (max ⌈B⌉₊ (2 * X.sup Int.natAbs + 1))
  refine ⟨q, hprime, (Nat.le_ceil B).trans (mod_cast (le_max_left _ _).trans hq),
    fun x hx ↦ ?_⟩
  have h₁ := le_sup (f := Int.natAbs) hx
  have h₂ := (le_max_right _ _).trans hq
  rw [Int.abs_eq_natAbs]
  omega

private lemma injOn_intCast {q : ℕ} {X : Finset ℤ} (hX : ∀ x ∈ X, 2 * |x| < q) :
    Set.InjOn (Int.cast : ℤ → ZMod q) X := by
  intro x hx y hy h
  have hdvd := (ZMod.intCast_eq_intCast_iff_dvd_sub x y q).1 h
  have hlt : |y - x| < q := by
    have := hX x hx
    have := hX y hy
    have := abs_sub y x
    linarith
  have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
  lia

private lemma card_image_intCast_add_le (q : ℕ) (X : Finset ℤ) :
    #(X.image (Int.cast : ℤ → ZMod q) + X.image (Int.cast : ℤ → ZMod q)) ≤ #(X + X) := by
  have h := image_add (Int.castAddHom (ZMod q)) (s := X) (t := X)
  simp only [Int.coe_castAddHom] at h
  rw [← h]
  exact card_image_le

private lemma exists_twoProperGAP_zmod {κ : ℝ} (hκ : 2 ≤ κ) {X : Finset ℤ}
    (hXX : (#(X + X) : ℝ) ≤ κ * #X) (hXlower : Real.exp (changContainerExponent κ) < #X) :
    ∃ (q : ℕ) (_ : NeZero q) (Q : GAP (ZMod q)), Q.TwoProper ∧ (∀ i, 1 < Q.length i) ∧
      (∀ x ∈ X, |x| < q) ∧ X.image (Int.cast : ℤ → ZMod q) ⊆ Q.carrier ∧
      (#Q.carrier : ℝ) ≤ Real.exp (changZModExponent κ) * #X := by
  obtain ⟨q, hq, hqB, hqX⟩ := exists_prime_ge X (Real.exp (changZModExponent κ) * #X)
  have h := exists_twoProperGAP_zmod_of_small_sumset (X.image (Int.cast : ℤ → ZMod q)) hq hκ
  rw [card_image_of_injOn (injOn_intCast hqX)] at h
  obtain ⟨Q, hQ, hXQ, hlen, -, hQcard⟩ :=
    h ((Nat.cast_le.2 (card_image_intCast_add_le q X)).trans hXX) hXlower hqB
  refine ⟨q, ⟨hq.pos.ne'⟩, Q, hQ, hlen, ?_, hXQ, hQcard⟩
  intro x hx
  linarith [hqX x hx, abs_nonneg x]

/-! ## Lifting a progression from `ZMod q` to `ℤ` -/

private lemma gapMap_snoc {d : ℕ} (o : ℤ) (s : Fin d → ℤ) (t : ℤ) (l : Fin (d + 1) → ℕ)
    (w : (i : Fin (d + 1)) → Fin (l i)) :
    gapMap o (Fin.snoc (α := fun _ ↦ ℤ) s t) l w =
      o + ∑ i : Fin d, ((w i.castSucc : ℕ) : ℤ) * s i + ((w (Fin.last d) : ℕ) : ℤ) * t := by
  simp [gapMap, Fin.sum_univ_castSucc, add_assoc]

private lemma intCast_gapMap_snoc {q d : ℕ} [NeZero q] {o' : ℤ} {o : ZMod q}
    (ho : (o' : ZMod q) = o) (s : Fin d → ZMod q) (l : Fin (d + 1) → ℕ)
    (w : (i : Fin (d + 1)) → Fin (l i)) :
    ((gapMap o' (Fin.snoc (α := fun _ ↦ ℤ) (fun i ↦ ((s i).val : ℤ)) q) l w : ℤ) : ZMod q) =
      gapMap o s (fun i ↦ l i.castSucc) fun i ↦ w i.castSucc := by
  rw [gapMap_snoc]
  simp [gapMap, ho]

private lemma injective_gapMap_snoc {q d : ℕ} [NeZero q] {o' : ℤ} {o : ZMod q}
    (ho : (o' : ZMod q) = o) (s : Fin d → ZMod q) (l : Fin (d + 1) → ℕ) {l' : Fin d → ℕ}
    (hl : ∀ i, l i.castSucc = l' i) (hinj : Function.Injective (gapMap o s l')) :
    Function.Injective
      (gapMap o' (Fin.snoc (α := fun _ ↦ ℤ) (fun i ↦ ((s i).val : ℤ)) q) l) := by
  obtain rfl : l' = fun i ↦ l i.castSucc := funext fun i ↦ (hl i).symm
  intro w w' h
  have hc : (fun i : Fin d ↦ w i.castSucc) = fun i : Fin d ↦ w' i.castSucc :=
    hinj ((intCast_gapMap_snoc ho s l w).symm.trans
      ((congrArg _ h).trans (intCast_gapMap_snoc ho s l w')))
  have hc' : ∀ i : Fin d, w i.castSucc = w' i.castSucc := congrFun hc
  rw [gapMap_snoc, gapMap_snoc] at h
  simp only [hc'] at h
  have hlast : ((w (Fin.last d) : ℕ) : ℤ) = (w' (Fin.last d) : ℕ) :=
    mul_right_cancel₀ (Nat.cast_ne_zero.2 (NeZero.ne q)) (by linarith)
  funext i
  refine Fin.lastCases ?_ (fun j ↦ hc' j) i
  exact Fin.ext (by exact_mod_cast hlast)

private lemma exists_gapMap_snoc_eq {d : ℕ} (o : ℤ) (s : Fin d → ℤ) (t : ℤ)
    (l : Fin (d + 1) → ℕ) {c : Fin d → ℕ} (hc : ∀ i, c i < l i.castSucc) {k : ℕ}
    (hk : k < l (Fin.last d)) :
    ∃ w : (i : Fin (d + 1)) → Fin (l i),
      gapMap o (Fin.snoc (α := fun _ ↦ ℤ) s t) l w = o + ∑ i, (c i : ℤ) * s i + k * t := by
  refine ⟨fun i ↦ ⟨Fin.snoc (α := fun _ ↦ ℕ) c k i, ?_⟩, ?_⟩
  · cases i using Fin.lastCases <;> simp [hc, hk]
  · simp [gapMap_snoc]

private lemma val_add_sum_lt {q d : ℕ} [NeZero q] (o : ZMod q) (s : Fin d → ZMod q)
    (l : Fin d → ℕ) (w : (i : Fin d) → Fin (l i)) :
    o.val + ∑ i, (w i : ℕ) * (s i).val < (∑ i, l i + 1) * q := by
  have h : ∑ i, (w i : ℕ) * (s i).val ≤ ∑ i, l i * q :=
    sum_le_sum fun i _ ↦ Nat.mul_le_mul (w i).2.le (ZMod.val_lt _).le
  rw [← sum_mul] at h
  have := ZMod.val_lt o
  rw [add_one_mul]
  linarith

private lemma exists_lift_coeff {q : ℕ} {x : ℤ} {y J : ℕ} (hx : |x| < q) (hy : y < J * q)
    (hdvd : (q : ℤ) ∣ y - x) : ∃ k : ℕ, k < J + 1 ∧ x = (y : ℤ) - J * q + k * q := by
  obtain ⟨j, hj⟩ := hdvd
  have hq : (0 : ℤ) < q := (abs_nonneg x).trans_lt hx
  have hy' : (y : ℤ) < J * q := mod_cast hy
  rw [abs_lt] at hx
  have hj0 : -1 < j := by nlinarith
  have hjJ : j < J + 1 := by nlinarith
  refine ⟨(J - j).toNat, by omega, ?_⟩
  rw [Int.toNat_of_nonneg (by omega)]
  linear_combination -hj

private noncomputable def liftGAP {q : ℕ} (Q : GAP (ZMod q)) : GAP ℤ where
  dim := Q.dim + 1
  carrier := univ.image (gapMap _ _ _)
  origin := (Q.origin.val : ℤ) - (∑ i, Q.length i + 1 : ℕ) * q
  step := Fin.snoc (α := fun _ ↦ ℤ) (fun i ↦ ((Q.step i).val : ℤ)) q
  length := Fin.snoc (α := fun _ ↦ ℕ) Q.length (∑ i, Q.length i + 2)
  length_pos i := by cases i using Fin.lastCases <;> simp [Q.length_pos]
  carrier_eq := rfl

private lemma liftGAP_twoProper {q : ℕ} [NeZero q] {Q : GAP (ZMod q)} (hQ : Q.TwoProper) :
    (liftGAP Q).TwoProper := by
  refine injective_gapMap_snoc (o := 2 • Q.origin) ?_ Q.step
    (fun i ↦ 2 * Fin.snoc (α := fun _ ↦ ℕ) Q.length (∑ i, Q.length i + 2) i)
    (fun i ↦ by simp) hQ
  simp [liftGAP]

private lemma mem_liftGAP {q : ℕ} [NeZero q] (Q : GAP (ZMod q)) {x : ℤ} (hx : |x| < q)
    (hxQ : (x : ZMod q) ∈ Q.carrier) : x ∈ (liftGAP Q).carrier := by
  set w := Q.coefficientsFin (x : ZMod q)
  have hspec : gapMap Q.origin Q.step Q.length w = x := Q.coefficientsFin_spec hxQ
  set y : ℕ := Q.origin.val + ∑ i, (w i : ℕ) * (Q.step i).val with hy
  have hycast : (x : ZMod q) = ((y : ℤ) : ZMod q) := by
    rw [← hspec]
    simp [hy, gapMap]
  obtain ⟨k, hk, hxk⟩ := exists_lift_coeff hx (val_add_sum_lt Q.origin Q.step Q.length w)
    ((ZMod.intCast_eq_intCast_iff_dvd_sub x y q).1 hycast)
  obtain ⟨w', hw'⟩ := exists_gapMap_snoc_eq (liftGAP Q).origin
    (fun i ↦ ((Q.step i).val : ℤ)) q (liftGAP Q).length (c := fun i ↦ w i)
    (fun i ↦ by simp [liftGAP]) (k := k) (by simp [liftGAP]; lia)
  refine (liftGAP Q).carrier_eq ▸ mem_image.2 ⟨w', mem_univ _, ?_⟩
  refine hw'.trans ?_
  rw [hxk]
  simp [liftGAP]
  ring

private lemma card_liftGAP_le {q : ℕ} (Q : GAP (ZMod q)) (hQ : Q.Proper) :
    #(liftGAP Q).carrier ≤ #Q.carrier * (∑ i, Q.length i + 2) := by
  rw [Q.card_eq_prod_length hQ]
  refine (liftGAP Q).card_le_prod_length.trans_eq ?_
  change ∏ i : Fin (Q.dim + 1),
    Fin.snoc (α := fun _ ↦ ℕ) Q.length (∑ i, Q.length i + 2) i = _
  simp [Fin.prod_univ_castSucc]

private lemma sum_add_two_le_two_mul_prod :
    ∀ {d : ℕ} (l : Fin d → ℕ), (∀ i, 1 < l i) → ∑ i, l i + 2 ≤ 2 * ∏ i, l i
  | 0, _, _ => by simp
  | d + 1, l, hl => by
    have ih := sum_add_two_le_two_mul_prod (fun i : Fin d ↦ l i.castSucc) fun i ↦ hl _
    have hp : 1 ≤ ∏ i : Fin d, l i.castSucc :=
      prod_pos fun (i : Fin d) _ ↦ zero_lt_one.trans (hl i.castSucc)
    have ha : 2 ≤ l (Fin.last d) := hl (Fin.last d)
    rw [Fin.sum_univ_castSucc, Fin.prod_univ_castSucc]
    linarith [Nat.mul_le_mul hp ha, Nat.mul_le_mul_left (∏ i : Fin d, l i.castSucc) ha,
      Nat.mul_le_mul_right (l (Fin.last d)) hp]

private lemma exists_twoProperGAP_int_of_zmod {q : ℕ} [NeZero q] {Q : GAP (ZMod q)}
    (hQ : Q.TwoProper) (hlen : ∀ i, 1 < Q.length i) {X : Finset ℤ} (hXq : ∀ x ∈ X, |x| < q)
    (hXQ : X.image (Int.cast : ℤ → ZMod q) ⊆ Q.carrier) :
    ∃ P : GAP ℤ, P.TwoProper ∧ X ⊆ P.carrier ∧ #P.carrier ≤ 2 * #Q.carrier ^ 2 := by
  refine ⟨liftGAP Q, liftGAP_twoProper hQ,
    fun x hx ↦ mem_liftGAP Q (hXq x hx) (hXQ (mem_image_of_mem _ hx)), ?_⟩
  have h₂ := sum_add_two_le_two_mul_prod Q.length hlen
  rw [← Q.card_eq_prod_length (Q.twoProper_proper hQ)] at h₂
  calc #(liftGAP Q).carrier
    _ ≤ #Q.carrier * (∑ i, Q.length i + 2) := card_liftGAP_le Q (Q.twoProper_proper hQ)
    _ ≤ #Q.carrier * (2 * #Q.carrier) := Nat.mul_le_mul_left _ h₂
    _ = 2 * #Q.carrier ^ 2 := by ring

/-! ## Chang's theorem -/

private lemma eight_le_exp_three : (8 : ℝ) ≤ Real.exp 3 := by
  have h : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h3]
  exact le_trans (by norm_num) (pow_le_pow_left₀ zero_le_two h 3)

private lemma two_mul_sq_le {a c x y z : ℝ} (hz : 0 ≤ z)
    (hzy : z ≤ Real.exp a * (Real.exp c * y)) (hyx : y ≤ 2 * Real.exp c * x) :
    2 * z ^ 2 ≤ Real.exp (2 * a + 4 * c + 3) * x ^ 2 := by
  have hz' : z ≤ 2 * (Real.exp a * Real.exp c ^ 2) * x :=
    hzy.trans ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hyx (Real.exp_pos c).le)
      (Real.exp_pos a).le).trans_eq (by ring))
  have h2 : Real.exp (2 * a) = Real.exp a ^ 2 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h4 : Real.exp (4 * c) = Real.exp c ^ 4 := by
    rw [← Real.exp_nat_mul]
    norm_num
  calc 2 * z ^ 2
    _ ≤ 2 * (2 * (Real.exp a * Real.exp c ^ 2) * x) ^ 2 := by gcongr
    _ = 8 * ((Real.exp a * Real.exp c ^ 2) ^ 2 * x ^ 2) := by ring
    _ ≤ Real.exp 3 * ((Real.exp a * Real.exp c ^ 2) ^ 2 * x ^ 2) := by
      gcongr
      exact eight_le_exp_three
    _ = Real.exp (2 * a + 4 * c + 3) * x ^ 2 := by
      rw [Real.exp_add, Real.exp_add, h2, h4]
      ring

/-- **Chang's theorem** for sets of integers: a finite nonempty `X ⊆ ℤ` with
`|X + X| ≤ κ * |X|` is contained in a `2`-proper GAP of size at most
`exp (changIntExponent κ) * |X| ^ 2`. -/
theorem exists_twoProperGAP_of_small_sumset {κ : ℝ} (X : Finset ℤ) (hX : X.Nonempty)
    (hκ : 2 ≤ κ) (hXX : (#(X + X) : ℝ) ≤ κ * #X) :
    ∃ P : GAP ℤ, P.TwoProper ∧ X ⊆ P.carrier ∧
      (#P.carrier : ℝ) ≤ Real.exp (changIntExponent κ) * (#X : ℝ) ^ 2 := by
  have hκ' : (2 : ℝ) ≤ 2 * κ := by linarith
  have hc := changContainerExponent_pos hκ'
  obtain ⟨X', hXX', hX'X', hX'lower, hX'upper⟩ :=
    exists_thickening hX hXX (Real.one_le_exp hc.le)
  obtain ⟨q, _, Q, hQ, hlen, hXq, hXQ, hQcard⟩ := exists_twoProperGAP_zmod hκ' hX'X' hX'lower
  obtain ⟨P, hP, hXP, hPcard⟩ := exists_twoProperGAP_int_of_zmod hQ hlen hXq hXQ
  refine ⟨P, hP, hXX'.trans hXP, ?_⟩
  have hPcard' : (#P.carrier : ℝ) ≤ 2 * (#Q.carrier : ℝ) ^ 2 := mod_cast hPcard
  rw [changZModExponent, Real.exp_add, mul_assoc] at hQcard
  have h := two_mul_sq_le (Nat.cast_nonneg _) hQcard hX'upper
  rw [changIntExponent, mul_assoc]
  exact hPcard'.trans h

end ChangFreimanRuzsa
