/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Combinatorics.Additive.FreimanHom
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Cast.Order

/-!
# Ruzsa's model lemma

A subset `X` of `ZMod q` with small doubling has a subset `X₁` of density `1 / s` in `X` that is
Freiman `s`-isomorphic to a subset of `ZMod m`, for any `m` with `#(s • X - s • X) ≤ m`. When
`#(X + X) ≤ κ * #X`, the Plünnecke–Ruzsa inequality allows `m ≤ κ ^ (2 * s) * #X`, so the density
of the image of `X₁` in `ZMod m` is bounded below in terms of `κ` and `s` alone.

The construction is Ruzsa's. Fix an invertible dilation `l` of `ZMod q`, which uses that `q` is
prime, and consider the integer representative `(l * x).val < q`. Splitting `Set.Ico 0 q` into `s`
intervals `Set.Ico (j * L) ((j + 1) * L)` of length `L = (q + s - 1) / s` and keeping the
interval `j` that contains the most dilated points produces `X₁` and the integer coordinate
`modelInt L j l x = (l * x).val - j * L`, which lies in `Set.Ico 0 L` and whose `s`-fold sums do
not wrap around modulo `q`. Reducing that coordinate modulo `m` is a Freiman `s`-isomorphism when
the dilation is good (`IsGoodDilation`): no nonzero element of `s • X - s • X` is dilated onto a
residue divisible by `m`. A good dilation exists by counting, because there are only
`#(s • X - s • X) ≤ m` elements to avoid and each of them rules out at most `(q - 1) / m`
dilations.

## Main statements

* `exists_subset_card_le_mul_card_isAddFreimanIso`: Ruzsa's model lemma over an arbitrary modulus
  `m` with `#(s • X - s • X) ≤ m`.
* `exists_subset_card_le_mul_card_isAddFreimanIso_of_card_add_le`: the same statement with the
  Plünnecke–Ruzsa bound `m ≤ κ ^ (2 * s) * #X` for the modulus.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open Finset
open scoped Pointwise

noncomputable section

namespace RuzsaModel

variable {q m s L j : ℕ}

/-! ### Good dilations -/

/-- A dilation `l` of `ZMod q` is `m`-good for `D` when no nonzero element of `D` is dilated onto a
residue whose representative is divisible by `m`. -/
def IsGoodDilation (m : ℕ) (D : Finset (ZMod q)) (l : ZMod q) : Prop :=
  ∀ d ∈ D, d ≠ 0 → ¬ m ∣ (l * d).val

lemma IsGoodDilation.subset {D D' : Finset (ZMod q)} {l : ZMod q} (h : IsGoodDilation m D l)
    (hsub : D' ⊆ D) : IsGoodDilation m D' l := fun d hd ↦ h d (hsub hd)

/-- The nonzero residues of `ZMod q` whose canonical representative is divisible by `m`. Each
nonzero element of `D` forbids the dilations landing in this set. -/
def dvdResidues (q m : ℕ) [NeZero q] : Finset (ZMod q) :=
  univ.filter fun y ↦ y ≠ 0 ∧ m ∣ y.val

lemma mem_dvdResidues [NeZero q] {y : ZMod q} : y ∈ dvdResidues q m ↔ y ≠ 0 ∧ m ∣ y.val := by
  simp [dvdResidues]

/-- There are at most `(q - 1) / m` nonzero residues with representative divisible by `m`. -/
lemma card_dvdResidues_le (q m : ℕ) [NeZero q] : #(dvdResidues q m) ≤ (q - 1) / m := by
  suffices h : #(dvdResidues q m) ≤ #(Icc 1 ((q - 1) / m)) by simpa using h
  apply card_le_card_of_injOn (fun y ↦ y.val / m)
  · intro y hy
    obtain ⟨hy0, hdvd⟩ := mem_dvdResidues.1 hy
    have hval : 0 < y.val := ZMod.val_pos.2 hy0
    simp only [coe_Icc, Set.mem_Icc]
    exact ⟨(Nat.one_le_div_iff (Nat.pos_of_dvd_of_pos hdvd hval)).2 (Nat.le_of_dvd hval hdvd),
      Nat.div_le_div_right (by grind [ZMod.val_lt y])⟩
  · intro y hy z hz hyz
    obtain ⟨-, hy⟩ := mem_dvdResidues.1 hy
    obtain ⟨-, hz⟩ := mem_dvdResidues.1 hz
    apply ZMod.val_injective q
    rw [← Nat.div_mul_cancel hy, ← Nat.div_mul_cancel hz]
    exact congrArg (· * m) hyz

/-- The dilations `l` that send some nonzero `d ∈ D` into `dvdResidues q m`. -/
def forbiddenDilations [NeZero q] (m : ℕ) (D : Finset (ZMod q)) : Finset (ZMod q) :=
  (D.erase 0).biUnion fun d ↦ (dvdResidues q m).image (· * d⁻¹)

lemma card_forbiddenDilations_le [NeZero q] (m : ℕ) (D : Finset (ZMod q)) :
    #(forbiddenDilations m D) ≤ #(D.erase 0) * #(dvdResidues q m) := by
  apply card_biUnion_le.trans
  simpa using sum_le_card_nsmul _ _ _ fun d _ ↦ card_image_le

/-- If `0 ∈ D` and `#D ≤ m`, fewer than `q - 1` dilations are forbidden. -/
lemma card_forbiddenDilations_lt [NeZero q] (hq : 2 ≤ q) {D : Finset (ZMod q)} (h0 : 0 ∈ D)
    (hD : #D ≤ m) : #(forbiddenDilations m D) < q - 1 := by
  have h := card_forbiddenDilations_le m D
  rw [card_erase_of_mem h0] at h
  rcases Nat.eq_zero_or_pos #(dvdResidues q m) with hK | hK
  · grind
  · have hKm : #(dvdResidues q m) * m ≤ q - 1 :=
      (Nat.mul_le_mul_right m (card_dvdResidues_le q m)).trans (Nat.div_mul_le_self _ _)
    grind [Nat.mul_le_mul_right #(dvdResidues q m) (Nat.sub_le_sub_right hD 1),
      Nat.sub_one_mul m #(dvdResidues q m)]

/-- A nonzero dilation outside `forbiddenDilations m D` is good. -/
lemma isGoodDilation_of_notMem_forbiddenDilations [Fact q.Prime] {D : Finset (ZMod q)}
    {l : ZMod q} (hl : l ≠ 0) (hlD : l ∉ forbiddenDilations m D) : IsGoodDilation m D l := by
  intro d hd hd0 hdvd
  apply hlD
  rw [forbiddenDilations, mem_biUnion]
  refine ⟨d, mem_erase.2 ⟨hd0, hd⟩, mem_image.2 ⟨l * d, ?_, mul_inv_cancel_right₀ hd0 l⟩⟩
  exact mem_dvdResidues.2 ⟨mul_ne_zero hl hd0, hdvd⟩

/-- A set `D` of at most `m` residues, containing `0`, admits a nonzero dilation that maps no
nonzero element of `D` onto a multiple of `m`.

A nonzero `d ∈ D` forbids only the dilations `l` with `l * d ∈ dvdResidues q m`, of which there
are at most `(q - 1) / m`, so at most `(#D - 1) * ((q - 1) / m) < q - 1` dilations are forbidden
altogether. -/
lemma exists_isGoodDilation (hq : q.Prime) {D : Finset (ZMod q)} (h0 : 0 ∈ D) (hD : #D ≤ m) :
    ∃ l : ZMod q, l ≠ 0 ∧ IsGoodDilation m D l := by
  have := Fact.mk hq
  obtain ⟨l, hl, hlD⟩ := exists_mem_notMem_of_card_lt_card
    (s := forbiddenDilations m D) (t := univ.erase 0)
    (by simpa using card_forbiddenDilations_lt hq.two_le h0 hD)
  exact ⟨l, ne_of_mem_erase hl,
    isGoodDilation_of_notMem_forbiddenDilations (ne_of_mem_erase hl) hlD⟩

/-! ### The model map -/

/-- The integer coordinate of the Ruzsa model: the representative of the dilated point, translated
so that the selected interval `Set.Ico (j * L) ((j + 1) * L)` starts at `0`. -/
def modelInt (L j : ℕ) (l x : ZMod q) : ℤ := ((l * x).val : ℤ) - j * L

/-- The Ruzsa model map: the integer coordinate `modelInt`, read in `ZMod m`. -/
def modelMap (m L j : ℕ) (l x : ZMod q) : ZMod m := (modelInt L j l x : ZMod m)

/-- The model coordinate of a point of the interval `j` is nonnegative. -/
lemma modelInt_nonneg {l x : ZMod q} (hx : (l * x).val / L = j) : 0 ≤ modelInt L j l x := by
  subst hx
  grind [modelInt, Nat.div_mul_le_self (l * x).val L]

/-- The model coordinate of a point of the interval `j` is smaller than the length `L`. -/
lemma modelInt_le (hL : 0 < L) {l x : ZMod q} (hx : (l * x).val / L = j) :
    modelInt L j l x ≤ L - 1 := by
  subst hx
  grind [modelInt, Nat.lt_div_mul_add (a := (l * x).val) hL]

/-- Read back in `ZMod q`, the model coordinate is the dilated point translated by `-(j * L)`. -/
lemma intCast_modelInt [NeZero q] (L j : ℕ) (l x : ZMod q) :
    (modelInt L j l x : ZMod q) = l * x - j * L := by
  simp [modelInt]

/-- The sum of the model coordinates of a multiset `σ`, read back in `ZMod q`, is
`l * σ.sum - card σ * (j * L)`. -/
lemma intCast_modelInt_sum [NeZero q] (L j : ℕ) (l : ZMod q) (σ : Multiset (ZMod q)) :
    ((σ.map (modelInt L j l)).sum : ZMod q) = l * σ.sum - Multiset.card σ * (j * L) := by
  induction σ using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons, Multiset.card_cons, Int.cast_add,
      intCast_modelInt, ih]
    push_cast
    ring

/-- For two multisets of the same size, the difference of the sums of their model coordinates is
congruent to the dilated difference of their sums modulo `q`. -/
lemma intCast_modelInt_sum_sub [NeZero q] (L j : ℕ) (l : ZMod q) {σ τ : Multiset (ZMod q)}
    (h : Multiset.card σ = Multiset.card τ) :
    (((σ.map (modelInt L j l)).sum - (τ.map (modelInt L j l)).sum : ℤ) : ZMod q) =
      l * (σ.sum - τ.sum) := by
  rw [Int.cast_sub, intCast_modelInt_sum, intCast_modelInt_sum, h]
  ring

/-- The model map is the integer coordinate read modulo `m`, so its multiset sums agree. -/
lemma intCast_modelInt_sum_eq_modelMap_sum (m L j : ℕ) (l : ZMod q) (σ : Multiset (ZMod q)) :
    ((σ.map (modelInt L j l)).sum : ZMod m) = (σ.map (modelMap m L j l)).sum := by
  induction σ using Multiset.induction_on with
  | empty => simp
  | cons a t ih => simp [modelMap, ih]

/-- The sum of `n` elements of `A` lies in the `n`-fold sumset of `A`. -/
lemma multiset_sum_mem_nsmul {G : Type*} [AddCommMonoid G] [DecidableEq G] {A : Finset G}
    {σ : Multiset G} (hσ : ∀ x ∈ σ, x ∈ A) : σ.sum ∈ Multiset.card σ • A := by
  induction σ using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.sum_cons, Multiset.card_cons, succ_nsmul']
    exact add_mem_add (hσ a (Multiset.mem_cons_self a t))
      (ih fun x hx ↦ hσ x (Multiset.mem_cons_of_mem hx))

/-- A good dilation forbids divisibility by `m` of the representative of a dilated nonzero
element, in the form used at the two signs of a difference of model sums. -/
lemma not_dvd_of_isGoodDilation [NeZero q] {D : Finset (ZMod q)} {l d : ZMod q}
    (hgood : IsGoodDilation m D l) (hd : d ∈ D) (hd0 : d ≠ 0) {u : ℤ} (hu0 : 0 < u)
    (huq : u < q) (hcong : (u : ZMod q) = l * d) : ¬ (m : ℤ) ∣ u := by
  intro hdvd
  refine hgood d hd hd0 (Int.natCast_dvd_natCast.1 ?_)
  rw [← hcong, ZMod.val_intCast, Int.emod_eq_of_lt hu0.le huq]
  exact hdvd

/-- The sum of the model coordinates of a multiset of elements of a single interval is
nonnegative. -/
lemma modelInt_sum_nonneg {A : Finset (ZMod q)} {l : ZMod q}
    (hA : ∀ x ∈ A, (l * x).val / L = j) {ρ : Multiset (ZMod q)} (hρ : ∀ x ∈ ρ, x ∈ A) :
    0 ≤ (ρ.map (modelInt L j l)).sum := by
  apply Multiset.sum_nonneg
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hz
  exact modelInt_nonneg (hA x (hρ x hx))

/-- The sum of the model coordinates of a multiset `ρ` of elements of a single interval is at most
`card ρ * (L - 1)`. -/
lemma modelInt_sum_le {A : Finset (ZMod q)} {l : ZMod q} (hL : 0 < L)
    (hA : ∀ x ∈ A, (l * x).val / L = j) {ρ : Multiset (ZMod q)} (hρ : ∀ x ∈ ρ, x ∈ A) :
    (ρ.map (modelInt L j l)).sum ≤ Multiset.card ρ * (L - 1 : ℤ) := by
  refine (Multiset.sum_le_card_nsmul _ (L - 1 : ℤ) ?_).trans_eq (by simp)
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hz
  exact modelInt_le hL (hA x (hρ x hx))

/-- For multisets of `s` elements of a single interval, with `s * L < q + s`, the difference of the
sums of model coordinates has absolute value less than `q`. -/
lemma abs_modelInt_sum_sub_lt {A : Finset (ZMod q)} {l : ZMod q} (hL : 0 < L)
    (hLwrap : s * L < q + s) (hA : ∀ x ∈ A, (l * x).val / L = j)
    {σ τ : Multiset (ZMod q)} (hσ : ∀ x ∈ σ, x ∈ A) (hτ : ∀ x ∈ τ, x ∈ A)
    (hcσ : Multiset.card σ = s) (hcτ : Multiset.card τ = s) :
    |(σ.map (modelInt L j l)).sum - (τ.map (modelInt L j l)).sum| < q := by
  rw [abs_lt]
  constructor <;> grind [modelInt_sum_le hL hA hσ, modelInt_sum_le hL hA hτ,
    modelInt_sum_nonneg hA hσ, modelInt_sum_nonneg hA hτ]

/-- For multisets `σ`, `τ` of `s` elements of a single interval with distinct sums, a positive
difference of the sums of model coordinates is not divisible by `m` when the dilation is good. -/
lemma not_dvd_modelInt_sum_sub_of_pos [NeZero q] {A : Finset (ZMod q)} {l : ZMod q} (hL : 0 < L)
    (hLwrap : s * L < q + s) (hA : ∀ x ∈ A, (l * x).val / L = j)
    (hgood : IsGoodDilation m (s • A - s • A) l) {σ τ : Multiset (ZMod q)}
    (hσ : ∀ x ∈ σ, x ∈ A) (hτ : ∀ x ∈ τ, x ∈ A) (hcσ : Multiset.card σ = s)
    (hcτ : Multiset.card τ = s) (hne : σ.sum ≠ τ.sum)
    (hpos : 0 < (σ.map (modelInt L j l)).sum - (τ.map (modelInt L j l)).sum) :
    ¬ (m : ℤ) ∣ (σ.map (modelInt L j l)).sum - (τ.map (modelInt L j l)).sum := by
  refine not_dvd_of_isGoodDilation hgood (sub_mem_sub (hcσ ▸ multiset_sum_mem_nsmul hσ)
    (hcτ ▸ multiset_sum_mem_nsmul hτ)) (sub_ne_zero.2 hne) hpos ?_
    (intCast_modelInt_sum_sub L j l (hcσ.trans hcτ.symm))
  exact (le_abs_self _).trans_lt (abs_modelInt_sum_sub_lt hL hLwrap hA hσ hτ hcσ hcτ)

/-- For multisets `σ`, `τ` of `s` elements of `A`, the difference of the two sums of model
coordinates is divisible by `m` if and only if the two multiset sums agree in `ZMod q`.

Both implications use that the difference of the two integer sums has absolute value less than
`q`. It is congruent to `l * (σ.sum - τ.sum)` modulo `q`, hence vanishes when the sums agree.
Conversely, a nonzero difference divisible by `m` would exhibit a nonzero element of
`s • A - s • A` dilated onto a multiple of `m`, which a good dilation forbids. -/
lemma dvd_modelInt_sum_sub_iff [NeZero q] {A : Finset (ZMod q)} {l : ZMod q} (hl : IsUnit l)
    (hL : 0 < L) (hLwrap : s * L < q + s) (hA : ∀ x ∈ A, (l * x).val / L = j)
    (hgood : IsGoodDilation m (s • A - s • A) l) {σ τ : Multiset (ZMod q)}
    (hσ : ∀ x ∈ σ, x ∈ A) (hτ : ∀ x ∈ τ, x ∈ A) (hcσ : Multiset.card σ = s)
    (hcτ : Multiset.card τ = s) :
    (m : ℤ) ∣ (σ.map (modelInt L j l)).sum - (τ.map (modelInt L j l)).sum ↔ σ.sum = τ.sum := by
  constructor
  · intro hdvd
    by_contra hne
    rcases lt_trichotomy ((σ.map (modelInt L j l)).sum - (τ.map (modelInt L j l)).sum) 0 with
      hneg | hzero | hpos
    · exact not_dvd_modelInt_sum_sub_of_pos hL hLwrap hA hgood hτ hσ hcτ hcσ (Ne.symm hne)
        (by grind) (dvd_sub_comm.1 hdvd)
    · apply hne
      rw [← sub_eq_zero, ← hl.mul_right_eq_zero,
        ← intCast_modelInt_sum_sub L j l (hcσ.trans hcτ.symm), hzero, Int.cast_zero]
    · exact not_dvd_modelInt_sum_sub_of_pos hL hLwrap hA hgood hσ hτ hcσ hcτ hne hpos hdvd
  · intro heq
    have hq : (q : ℤ) ∣ (σ.map (modelInt L j l)).sum - (τ.map (modelInt L j l)).sum := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, intCast_modelInt_sum_sub L j l (hcσ.trans hcτ.symm),
        heq, sub_self, mul_zero]
    simp [Int.eq_zero_of_abs_lt_dvd hq (abs_modelInt_sum_sub_lt hL hLwrap hA hσ hτ hcσ hcτ)]

/-- For multisets `σ`, `τ` of `s` elements of `A`, the sums of their images under the model map
agree if and only if their sums agree. -/
lemma modelMap_sum_eq_iff [NeZero q] {A : Finset (ZMod q)} {l : ZMod q} (hl : IsUnit l)
    (hL : 0 < L) (hLwrap : s * L < q + s) (hA : ∀ x ∈ A, (l * x).val / L = j)
    (hgood : IsGoodDilation m (s • A - s • A) l) {σ τ : Multiset (ZMod q)}
    (hσ : ∀ x ∈ σ, x ∈ A) (hτ : ∀ x ∈ τ, x ∈ A) (hcσ : Multiset.card σ = s)
    (hcτ : Multiset.card τ = s) :
    (σ.map (modelMap m L j l)).sum = (τ.map (modelMap m L j l)).sum ↔ σ.sum = τ.sum := by
  rw [← intCast_modelInt_sum_eq_modelMap_sum, ← intCast_modelInt_sum_eq_modelMap_sum,
    ← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact dvd_modelInt_sum_sub_iff hl hL hLwrap hA hgood hσ hτ hcσ hcτ

/-- For `0 < s`, the model map is injective on `A`. -/
lemma injOn_modelMap [NeZero q] {A : Finset (ZMod q)} {l : ZMod q} (hl : IsUnit l) (hs : 0 < s)
    (hL : 0 < L) (hLwrap : s * L < q + s) (hA : ∀ x ∈ A, (l * x).val / L = j)
    (hgood : IsGoodDilation m (s • A - s • A) l) : Set.InjOn (modelMap m L j l) A := by
  rintro x (hx : x ∈ A) y (hy : y ∈ A) hxy
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  simpa using (modelMap_sum_eq_iff hl hL hLwrap hA hgood
    (σ := x ::ₘ Multiset.replicate n y) (τ := y ::ₘ Multiset.replicate n y)
    (by simp [Multiset.mem_replicate, hx, hy]) (by simp [Multiset.mem_replicate, hy])
    (by simp) (by simp)).1 (by simp [hxy])

/-- On a set `A` all of whose dilates land in the same interval of length `L`, and for a good
dilation, reduction of the model coordinate modulo `m` is a Freiman `s`-isomorphism onto its
image. -/
lemma isAddFreimanIso_modelMap [NeZero q] {A : Finset (ZMod q)} {l : ZMod q} (hl : IsUnit l)
    (hs : 0 < s) (hL : 0 < L) (hLwrap : s * L < q + s) (hA : ∀ x ∈ A, (l * x).val / L = j)
    (hgood : IsGoodDilation m (s • A - s • A) l) :
    IsAddFreimanIso s (A : Set (ZMod q)) (A.image (modelMap m L j l) : Set (ZMod m))
      (modelMap m L j l) := by
  refine ⟨?_, fun σ τ hσ hτ hcσ hcτ ↦ modelMap_sum_eq_iff hl hL hLwrap hA hgood hσ hτ hcσ hcτ⟩
  rw [coe_image]
  exact (injOn_modelMap hl hs hL hLwrap hA hgood).bijOn_image

/-- For `0 < s` and `2 ≤ q`, there is an interval length `0 < L` with `q ≤ s * L < q + s`. -/
lemma exists_pos_le_mul_lt_add (hs : 0 < s) (hq : 2 ≤ q) : ∃ L, 0 < L ∧ q ≤ s * L ∧ s * L < q + s :=
  ⟨(q + s - 1) / s, (Nat.one_le_div_iff hs).2 (by grind), by
    grind [Nat.div_add_mod (q + s - 1) s, Nat.mod_lt (q + s - 1) hs], by
    grind [Nat.div_add_mod (q + s - 1) s]⟩

/-- If `s` intervals of length `L` cover `Set.Ico 0 q`, one of them contains at least a proportion
`1 / s` of the dilates of `X`. -/
lemma exists_card_le_mul_card_filter [NeZero q] (hs : 0 < s) (hL : 0 < L) (hcover : q ≤ s * L)
    (X : Finset (ZMod q)) (l : ZMod q) : ∃ j, #X ≤ s * #{x ∈ X | (l * x).val / L = j} := by
  obtain ⟨j, -, hj⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (f := fun x ↦ (l * x).val / L) (t := range s) (b := (#X : ℚ) / s)
    (fun x _ ↦ mem_range.2 ((Nat.div_lt_iff_lt_mul hL).2 ((ZMod.val_lt _).trans_le hcover)))
    ⟨0, mem_range.2 hs⟩ (by simp [field])
  refine ⟨j, ?_⟩
  rw [mul_comm]
  exact_mod_cast (div_le_iff₀ (by positivity : (0 : ℚ) < s)).1 hj

end RuzsaModel

open RuzsaModel

/-- **Ruzsa's model lemma.** A nonempty `X : Finset (ZMod q)`, `q` prime, has a subset `X₁` of
density at least `1 / s` which is Freiman `s`-isomorphic to a subset of `ZMod m`, for any modulus
`m` with `#(s • X - s • X) ≤ m`.

Only the invertibility of the dilation uses that `q` is prime. -/
lemma exists_subset_card_le_mul_card_isAddFreimanIso {q s m : ℕ} (hq : q.Prime) (hs : 0 < s)
    {X : Finset (ZMod q)} (hX : X.Nonempty) (hm : #(s • X - s • X) ≤ m) :
    ∃ X₁ ⊆ X, #X ≤ s * #X₁ ∧ ∃ φ : ZMod q → ZMod m,
      IsAddFreimanIso s (X₁ : Set (ZMod q)) (X₁.image φ : Set (ZMod m)) φ := by
  have := Fact.mk hq
  obtain ⟨l, hl0, hgood⟩ := exists_isGoodDilation hq hX.nsmul.zero_mem_sub hm
  obtain ⟨L, hL, hcover, hwrap⟩ := exists_pos_le_mul_lt_add hs hq.two_le
  obtain ⟨j, hj⟩ := exists_card_le_mul_card_filter hs hL hcover X l
  refine ⟨_, filter_subset _ _, hj, modelMap m L j l,
    isAddFreimanIso_modelMap (isUnit_iff_ne_zero.2 hl0) hs hL hwrap (by simp) (hgood.subset ?_)⟩
  gcongr
  all_goals exact filter_subset _ _

/-- Ruzsa's model lemma with the Plünnecke–Ruzsa bound on the modulus. If `#(X + X) ≤ κ * #X`,
the model group can be taken of size at most `κ ^ (2 * s) * #X`. The image of `X₁` then has
density at least `(s * κ ^ (2 * s))⁻¹` in `ZMod m`, a bound independent of `q`. -/
lemma exists_subset_card_le_mul_card_isAddFreimanIso_of_card_add_le {q s : ℕ} {κ : ℝ}
    (hq : q.Prime) (hs : 0 < s) {X : Finset (ZMod q)} (hX : X.Nonempty)
    (hXX : (#(X + X) : ℝ) ≤ κ * #X) :
    ∃ (m : ℕ) (X₁ : Finset (ZMod q)) (φ : ZMod q → ZMod m),
      0 < m ∧ (m : ℝ) ≤ κ ^ (2 * s) * #X ∧ X₁ ⊆ X ∧ #X ≤ s * #X₁ ∧
      IsAddFreimanIso s (X₁ : Set (ZMod q)) (X₁.image φ : Set (ZMod m)) φ := by
  obtain ⟨X₁, hX₁, hcard, φ, hφ⟩ :=
    exists_subset_card_le_mul_card_isAddFreimanIso hq hs hX le_rfl
  refine ⟨#(s • X - s • X), X₁, φ, card_pos.2 ⟨0, hX.nsmul.zero_mem_sub⟩, ?_, hX₁, hcard, hφ⟩
  have h := (NNRat.cast_le (K := ℝ)).2 (pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hX X s s)
  push_cast at h
  refine h.trans ?_
  rw [two_mul]
  gcongr
  exact (div_le_iff₀ (Nat.cast_pos.2 hX.card_pos)).2 hXX

end

end ChangFreimanRuzsa
