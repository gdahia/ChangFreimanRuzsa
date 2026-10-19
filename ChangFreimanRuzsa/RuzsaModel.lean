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

/-! # Ruzsa's model lemma

A subset $X$ of $\mathbb{Z}/q\mathbb{Z}$ with small doubling has a subset $X_1$ of density $1/s$
in $X$ that is Freiman $s$-isomorphic to a subset of $\mathbb{Z}/m\mathbb{Z}$, for any
$m \ge |sX - sX|$. When $|X + X| \le \kappa |X|$, the Plünnecke–Ruzsa inequality allows
$m \le \kappa^{2s} |X|$, so the density of the image of $X_1$ in $\mathbb{Z}/m\mathbb{Z}$ is
bounded below in terms of $\kappa$ and $s$ alone.

The construction is Ruzsa's. Fix an invertible dilation $l$ of $\mathbb{Z}/q\mathbb{Z}$, which
uses that $q$ is prime, and consider the integer representative $(l x).\mathrm{val} \in [0, q)$.
Splitting $[0, q)$ into $s$ buckets of length $L = \lceil q / s \rceil$ and keeping the most
populated bucket $j$ produces $X_1$ and the integer coordinate
$$\mathtt{modelInt}\ L\ j\ l\ x = (l x).\mathrm{val} - j L \in [0, L),$$
whose $s$-fold sums do not wrap around modulo $q$. Reducing that coordinate modulo $m$ is a Freiman
$s$-isomorphism when the dilation is good (`IsGoodDilation`): no nonzero element of $sX - sX$ is
dilated onto a residue divisible by $m$. A good dilation exists by counting, because there are only
$|sX - sX| \le m$ elements to avoid and each of them rules out at most $(q - 1) / m$ dilations.

## Main results

* `exists_ruzsa_model`: the model over an arbitrary modulus $m \ge |sX - sX|$.
* `exists_ruzsa_model_of_doubling`: the same statement with the Plünnecke–Ruzsa bound
  $m \le \kappa^{2s} |X|$ for the modulus.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open scoped Pointwise

noncomputable section

namespace RuzsaModel

variable {q m s L j : ℕ}

/-! ### Good dilations -/

/-- A dilation $l$ of $\mathbb{Z}/q\mathbb{Z}$ is $m$-good for $D$ when no nonzero element of $D$
is dilated onto a residue whose representative is divisible by $m$. -/
def IsGoodDilation (m : ℕ) (D : Finset (ZMod q)) (l : ZMod q) : Prop :=
  ∀ d ∈ D, d ≠ 0 → ¬ m ∣ (l * d).val

lemma IsGoodDilation.subset {D D' : Finset (ZMod q)} {l : ZMod q} (h : IsGoodDilation m D l)
    (hsub : D' ⊆ D) : IsGoodDilation m D' l := fun d hd ↦ h d (hsub hd)

/-- The nonzero residues of `ZMod q` whose canonical representative is divisible by `m`. Each
nonzero element of `D` forbids the dilations landing in this set. -/
def dvdResidues (q m : ℕ) [NeZero q] : Finset (ZMod q) :=
  Finset.univ.filter fun y ↦ y ≠ 0 ∧ m ∣ y.val

lemma mem_dvdResidues [NeZero q] {y : ZMod q} : y ∈ dvdResidues q m ↔ y ≠ 0 ∧ m ∣ y.val := by
  simp [dvdResidues]

/-- There are at most `(q - 1) / m` nonzero residues with representative divisible by `m`. -/
lemma card_dvdResidues_le [NeZero q] : (dvdResidues q m).card ≤ (q - 1) / m := by
  suffices h : (dvdResidues q m).card ≤ (Finset.Icc 1 ((q - 1) / m)).card by simpa using h
  apply Finset.card_le_card_of_injOn (fun y ↦ y.val / m)
  · intro y hy
    obtain ⟨hy0, hdvd⟩ := mem_dvdResidues.1 hy
    have hval : 0 < y.val := ZMod.val_pos.2 hy0
    simp only [Finset.coe_Icc, Set.mem_Icc]
    exact ⟨(Nat.one_le_div_iff (Nat.pos_of_dvd_of_pos hdvd hval)).2 (Nat.le_of_dvd hval hdvd),
      Nat.div_le_div_right (by grind [ZMod.val_lt y])⟩
  · intro y hy z hz hyz
    obtain ⟨-, hy⟩ := mem_dvdResidues.1 hy
    obtain ⟨-, hz⟩ := mem_dvdResidues.1 hz
    apply ZMod.val_injective q
    rw [← Nat.div_mul_cancel hy, ← Nat.div_mul_cancel hz]
    exact congrArg (· * m) hyz

/-- A set $D$ of at most $m$ residues, containing $0$, admits a nonzero dilation that maps no
nonzero element of $D$ onto a multiple of $m$.

A nonzero $d \in D$ forbids only the dilations $l$ with $l d \in$ `dvdResidues q m`, of which
there are at most $(q - 1) / m$, so at most $(|D| - 1) \lfloor (q - 1) / m \rfloor < q - 1$
dilations are forbidden altogether. -/
lemma exists_isGoodDilation (hq : q.Prime) {D : Finset (ZMod q)} (h0 : (0 : ZMod q) ∈ D)
    (hD : D.card ≤ m) : ∃ l : ZMod q, l ≠ 0 ∧ IsGoodDilation m D l := by
  have : NeZero q := ⟨hq.pos.ne'⟩
  have := Fact.mk hq
  have hq2 : 2 ≤ q := hq.two_le
  have hDpos : 0 < D.card := Finset.card_pos.2 ⟨0, h0⟩
  have hcard : ((D.erase 0).biUnion fun d ↦ (dvdResidues q m).image (· * d⁻¹)).card
      < (Finset.univ.erase (0 : ZMod q)).card := by
    have hbiUnion : ((D.erase 0).biUnion fun d ↦ (dvdResidues q m).image (· * d⁻¹)).card
        ≤ (D.card - 1) * (dvdResidues q m).card := by
      apply Finset.card_biUnion_le.trans
      apply le_trans (Finset.sum_le_card_nsmul _ _ _ fun d _ ↦ Finset.card_image_le)
      rw [Finset.card_erase_of_mem h0, smul_eq_mul]
    have hdvd : (dvdResidues q m).card * m ≤ q - 1 :=
      le_trans (Nat.mul_le_mul_right m card_dvdResidues_le) (Nat.div_mul_le_self _ _)
    have hmono : (D.card - 1) * (dvdResidues q m).card
        ≤ (m - 1) * (dvdResidues q m).card := Nat.mul_le_mul_right _ (by grind)
    have hsub : (m - 1) * (dvdResidues q m).card
        = (dvdResidues q m).card * m - (dvdResidues q m).card := by
      rw [Nat.sub_mul, Nat.one_mul, Nat.mul_comm]
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
    rcases Nat.eq_zero_or_pos (dvdResidues q m).card with hK | hK
    · rw [hK, Nat.mul_zero] at hbiUnion
      grind
    · grind
  obtain ⟨l, hl, hlbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨l, Finset.ne_of_mem_erase hl, ?_⟩
  intro d hd hd0 hdvd
  refine hlbad (Finset.mem_biUnion.2 ⟨d, Finset.mem_erase.2 ⟨hd0, hd⟩, ?_⟩)
  refine Finset.mem_image.2 ⟨l * d, ?_, mul_inv_cancel_right₀ hd0 l⟩
  exact mem_dvdResidues.2 ⟨mul_ne_zero (Finset.ne_of_mem_erase hl) hd0, hdvd⟩

/-- The `n`-fold difference set of a nonempty set contains `0`. -/
lemma zero_mem_nsmul_sub_nsmul {G : Type*} [AddCommGroup G] [DecidableEq G] {A : Finset G}
    (hA : A.Nonempty) (n : ℕ) : (0 : G) ∈ n • A - n • A := by
  obtain ⟨x, hx⟩ := hA
  simpa using Finset.sub_mem_sub (Finset.nsmul_mem_nsmul (n := n) hx)
    (Finset.nsmul_mem_nsmul (n := n) hx)

/-! ### The model map -/

/-- The integer coordinate of the Ruzsa model: the representative of the dilated point, translated
so that the selected bucket of length `L` starts at `0`. -/
def modelInt (L j : ℕ) (l x : ZMod q) : ℤ := ((l * x).val : ℤ) - j * L

/-- The Ruzsa model map: the integer coordinate `modelInt`, read in `ZMod m`. -/
def modelMap (m L j : ℕ) (l x : ZMod q) : ZMod m := (modelInt L j l x : ZMod m)

/-- Membership in the bucket `j` of length `L` bounds the representative from both sides. -/
lemma bucket_bounds (hL : 0 < L) {v : ℕ} (hv : v / L = j) : j * L ≤ v ∧ v < j * L + L := by
  subst hv
  grind [Nat.div_add_mod v L, Nat.mod_lt v hL]

/-- The model coordinate of a point of the bucket `j` is nonnegative. -/
lemma modelInt_nonneg (hL : 0 < L) {l x : ZMod q} (hx : (l * x).val / L = j) :
    0 ≤ modelInt L j l x := by
  obtain ⟨h, -⟩ := bucket_bounds hL hx
  rw [modelInt]
  grind

/-- The model coordinate of a point of the bucket `j` is smaller than the bucket length. -/
lemma modelInt_le (hL : 0 < L) {l x : ZMod q} (hx : (l * x).val / L = j) :
    modelInt L j l x ≤ (L : ℤ) - 1 := by
  obtain ⟨-, h⟩ := bucket_bounds hL hx
  rw [modelInt]
  grind

/-- Read back in `ZMod q`, the model coordinate is the dilated point translated by the start of the
bucket. -/
lemma natCast_modelInt [NeZero q] (l x : ZMod q) :
    ((modelInt L j l x : ℤ) : ZMod q) = l * x - (j : ZMod q) * L := by
  simp [modelInt]

/-- The sum of the model coordinates of a multiset, read back in `ZMod q`, recovers the dilated sum
of the multiset up to the bucket translation. -/
lemma natCast_modelInt_sum [NeZero q] (l : ZMod q) (σ : Multiset (ZMod q)) :
    (((σ.map (modelInt L j l)).sum : ℤ) : ZMod q)
      = l * σ.sum - (Multiset.card σ : ZMod q) * (j * L) := by
  induction σ using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons, Multiset.card_cons, Int.cast_add,
      natCast_modelInt, ih]
    push_cast
    ring

/-- The model map is the integer coordinate read modulo `m`, so its multiset sums agree. -/
lemma intCast_modelInt_sum (l : ZMod q) (σ : Multiset (ZMod q)) :
    (((σ.map (modelInt L j l)).sum : ℤ) : ZMod m) = (σ.map (modelMap m L j l)).sum := by
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
    exact Finset.add_mem_add (hσ a (Multiset.mem_cons_self a t))
      (ih fun x hx ↦ hσ x (Multiset.mem_cons_of_mem hx))

/-- A good dilation forbids divisibility by `m` of the representative of a dilated nonzero
element, in the form used at the two signs of a difference of model sums. -/
lemma not_dvd_of_isGoodDilation [NeZero q] {D : Finset (ZMod q)} {l d : ZMod q}
    (hgood : IsGoodDilation m D l) (hd : d ∈ D) (hd0 : d ≠ 0) {u : ℤ} (hu0 : 0 < u)
    (huq : u < q) (hcong : ((u : ℤ) : ZMod q) = l * d) : ¬ (m : ℤ) ∣ u := by
  intro hdvd
  refine hgood d hd hd0 (Int.natCast_dvd_natCast.1 ?_)
  rw [← hcong, ZMod.val_intCast, Int.emod_eq_of_lt hu0.le huq]
  exact hdvd

/-- The sum of the model coordinates of a multiset of elements of a single bucket lies in
$[0, |\rho| (L - 1)]$. For multisets of $s$ elements this keeps the difference of two such sums
inside $(-q, q)$. -/
lemma modelInt_sum_bounds [NeZero q] {A : Finset (ZMod q)} {l : ZMod q} (hL : 0 < L)
    (hbucket : ∀ x ∈ A, (l * x).val / L = j) {ρ : Multiset (ZMod q)} (hρ : ∀ x ∈ ρ, x ∈ A) :
    0 ≤ (ρ.map (modelInt L j l)).sum ∧
      (ρ.map (modelInt L j l)).sum ≤ (Multiset.card ρ : ℤ) * ((L : ℤ) - 1) := by
  constructor
  · apply Multiset.sum_nonneg
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hz
    exact modelInt_nonneg hL (hbucket x (hρ x hx))
  · refine le_trans (Multiset.sum_le_card_nsmul _ ((L : ℤ) - 1) ?_) ?_
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hz
      exact modelInt_le hL (hbucket x (hρ x hx))
    · rw [Multiset.card_map, nsmul_eq_mul]

/-- For multisets $\sigma, \tau$ of $s$ elements of $A$, the difference of the two sums of model
coordinates is divisible by $m$ if and only if the two multiset sums agree in
$\mathbb{Z}/q\mathbb{Z}$.

Both implications use that the difference of the two integer sums lies in $(-q, q)$. It is
congruent to $l (\sum \sigma - \sum \tau)$ modulo $q$, hence vanishes when the sums agree.
Conversely, a nonzero difference divisible by $m$ would exhibit a nonzero element of $sA - sA$
dilated onto a multiple of $m$, which a good dilation forbids. -/
lemma dvd_modelInt_sum_sub_iff [NeZero q] {A : Finset (ZMod q)} {l : ZMod q} (hl : IsUnit l)
    (hL : 0 < L) (hLwrap : s * L < q + s) (hbucket : ∀ x ∈ A, (l * x).val / L = j)
    (hgood : IsGoodDilation m (s • A - s • A) l) {σ τ : Multiset (ZMod q)}
    (hσ : ∀ x ∈ σ, x ∈ A) (hτ : ∀ x ∈ τ, x ∈ A) (hcσ : Multiset.card σ = s)
    (hcτ : Multiset.card τ = s) :
    (m : ℤ) ∣ (σ.map (modelInt L j l)).sum - (τ.map (modelInt L j l)).sum ↔ σ.sum = τ.sum := by
  have hwrap : (s : ℤ) * ((L : ℤ) - 1) < q := by
    rw [mul_sub, mul_one]
    grind
  have hcong : ∀ ρ ρ' : Multiset (ZMod q), Multiset.card ρ = s → Multiset.card ρ' = s →
      ((((ρ.map (modelInt L j l)).sum - (ρ'.map (modelInt L j l)).sum : ℤ)) : ZMod q)
        = l * (ρ.sum - ρ'.sum) := by
    intro ρ ρ' hcρ hcρ'
    rw [Int.cast_sub, natCast_modelInt_sum, natCast_modelInt_sum, hcρ, hcρ']
    ring
  have key : ∀ ρ ρ' : Multiset (ZMod q), (∀ x ∈ ρ, x ∈ A) → (∀ x ∈ ρ', x ∈ A) →
      Multiset.card ρ = s → Multiset.card ρ' = s → ρ.sum ≠ ρ'.sum →
      0 < (ρ.map (modelInt L j l)).sum - (ρ'.map (modelInt L j l)).sum →
      ¬ (m : ℤ) ∣ (ρ.map (modelInt L j l)).sum - (ρ'.map (modelInt L j l)).sum := by
    intro ρ ρ' hρ hρ' hcρ hcρ' hne hpos
    obtain ⟨-, hub⟩ := modelInt_sum_bounds hL hbucket hρ
    obtain ⟨hlb, -⟩ := modelInt_sum_bounds hL hbucket hρ'
    rw [hcρ] at hub
    exact not_dvd_of_isGoodDilation hgood (Finset.sub_mem_sub (hcρ ▸ multiset_sum_mem_nsmul hρ)
      (hcρ' ▸ multiset_sum_mem_nsmul hρ')) (sub_ne_zero.2 hne) hpos (by grind)
      (hcong ρ ρ' hcρ hcρ')
  constructor
  · intro hdvd
    by_contra hne
    rcases lt_trichotomy ((σ.map (modelInt L j l)).sum - (τ.map (modelInt L j l)).sum) 0 with
      hneg | hzero | hpos
    · refine key τ σ hτ hσ hcτ hcσ (Ne.symm hne) (by grind) ?_
      rw [← neg_sub]
      exact dvd_neg.2 hdvd
    · refine hne (sub_eq_zero.1 (hl.mul_right_eq_zero.1 ?_))
      rw [← hcong σ τ hcσ hcτ, hzero, Int.cast_zero]
    · exact key σ τ hσ hτ hcσ hcτ hne hpos hdvd
  · intro heq
    obtain ⟨hlb, hub⟩ := modelInt_sum_bounds hL hbucket hσ
    obtain ⟨hlb', hub'⟩ := modelInt_sum_bounds hL hbucket hτ
    rw [hcσ] at hub
    rw [hcτ] at hub'
    have hqdvd : ((q : ℕ) : ℤ) ∣ (σ.map (modelInt L j l)).sum - (τ.map (modelInt L j l)).sum := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hcong σ τ hcσ hcτ, heq, sub_self, mul_zero]
    rw [Int.eq_zero_of_abs_lt_dvd hqdvd (abs_lt.2 ⟨by grind, by grind⟩)]
    exact dvd_zero _

/-- On a set $A$ all of whose dilates land in the same bucket of length $L$, and for a good
dilation, reduction of the model coordinate modulo $m$ is a Freiman $s$-isomorphism onto its
image. -/
lemma isAddFreimanIso_modelMap [NeZero q] {A : Finset (ZMod q)} {l : ZMod q} (hl : IsUnit l)
    (hs : 0 < s) (hL : 0 < L) (hLwrap : s * L < q + s) (hbucket : ∀ x ∈ A, (l * x).val / L = j)
    (hgood : IsGoodDilation m (s • A - s • A) l) :
    IsAddFreimanIso s (A : Set (ZMod q)) (A.image (modelMap m L j l) : Set (ZMod m))
      (modelMap m L j l) := by
  have hsum : ∀ σ τ : Multiset (ZMod q), (∀ x ∈ σ, x ∈ A) → (∀ x ∈ τ, x ∈ A) →
      Multiset.card σ = s → Multiset.card τ = s →
      ((σ.map (modelMap m L j l)).sum = (τ.map (modelMap m L j l)).sum ↔ σ.sum = τ.sum) := by
    intro σ τ hσ hτ hcσ hcτ
    rw [← intCast_modelInt_sum, ← intCast_modelInt_sum, ← sub_eq_zero, ← Int.cast_sub,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_modelInt_sum_sub_iff hl hL hLwrap hbucket hgood hσ hτ hcσ hcτ
  have hinj : Set.InjOn (modelMap m L j l) (A : Set (ZMod q)) := by
    rintro x (hx : x ∈ A) y (hy : y ∈ A) hxy
    have hnsmul : (s : ℕ) • y = (s - 1) • y + y := by
      rw [← succ_nsmul, Nat.sub_add_cancel hs]
    have heq := (hsum (x ::ₘ Multiset.replicate (s - 1) y) (Multiset.replicate s y)
      (by simp [Multiset.mem_replicate, hx, hy]) (by simp [Multiset.mem_replicate, hy])
      (by grind [Multiset.card_cons, Multiset.card_replicate]) (Multiset.card_replicate s y)).1 ?_
    · rw [Multiset.sum_cons, Multiset.sum_replicate, Multiset.sum_replicate, hnsmul,
        add_comm] at heq
      exact add_left_cancel heq
    · rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_replicate, Multiset.map_replicate,
        Multiset.sum_replicate, Multiset.sum_replicate, hxy, ← succ_nsmul', Nat.sub_add_cancel hs]
  constructor
  · rw [Finset.coe_image]
    exact hinj.bijOn_image
  · intro σ τ hσ hτ hcσ hcτ
    exact hsum σ τ hσ hτ hcσ hcτ

end RuzsaModel

open RuzsaModel

/-- **Ruzsa's model lemma.** A nonempty $X \subseteq \mathbb{Z}/q\mathbb{Z}$, $q$ prime, has a
subset $X_1$ of density at least $1 / s$ which is Freiman $s$-isomorphic to a subset of
$\mathbb{Z}/m\mathbb{Z}$, for any modulus $m \ge |sX - sX|$.

Only the invertibility of the dilation uses that $q$ is prime. -/
lemma exists_ruzsa_model {q s m : ℕ} (hq : q.Prime) (hs : 0 < s) {X : Finset (ZMod q)}
    (hX : X.Nonempty) (hm : (s • X - s • X).card ≤ m) :
    ∃ X₁ ⊆ X, X.card ≤ s * X₁.card ∧ ∃ φ : ZMod q → ZMod m,
      IsAddFreimanIso s (X₁ : Set (ZMod q)) (X₁.image φ : Set (ZMod m)) φ := by
  have : NeZero q := ⟨hq.pos.ne'⟩
  have := Fact.mk hq
  obtain ⟨l, hl0, hgood⟩ := exists_isGoodDilation hq (zero_mem_nsmul_sub_nsmul hX s) hm
  obtain ⟨L, hL, hcover, hwrap⟩ : ∃ L, 0 < L ∧ q ≤ s * L ∧ s * L < q + s := by
    refine ⟨(q + s - 1) / s, (Nat.one_le_div_iff hs).2 ?_, ?_, ?_⟩ <;>
      grind [Nat.div_add_mod (q + s - 1) s, Nat.mod_lt (q + s - 1) hs, hq.two_le]
  have hmaps : ∀ x ∈ X, (l * x).val / L ∈ Finset.range s := by
    intro x _
    refine Finset.mem_range.2 ((Nat.div_lt_iff_lt_mul hL).2 ?_)
    exact lt_of_lt_of_le (ZMod.val_lt _) hcover
  have hb : (Finset.range s).card • ((X.card : ℚ) / s) ≤ (X.card : ℚ) := by
    rw [Finset.card_range, nsmul_eq_mul,
      mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hs.ne' : (s : ℚ) ≠ 0)]
  obtain ⟨j, -, hjcard⟩ :=
    Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmaps ⟨0, Finset.mem_range.2 hs⟩ hb
  refine ⟨{x ∈ X | (l * x).val / L = j}, Finset.filter_subset _ _, ?_, modelMap m L j l, ?_⟩
  · rw [Nat.mul_comm]
    exact_mod_cast (div_le_iff₀ (Nat.cast_pos.2 hs : (0 : ℚ) < s)).1 hjcard
  · refine isAddFreimanIso_modelMap (isUnit_iff_ne_zero.2 hl0) hs hL hwrap ?_
      (hgood.subset (Finset.sub_subset_sub ?_ ?_))
    · simp
    · exact Finset.nsmul_subset_nsmul_left (Finset.filter_subset _ _)
    · exact Finset.nsmul_subset_nsmul_left (Finset.filter_subset _ _)

/-- Ruzsa's model lemma with the Plünnecke–Ruzsa bound on the modulus. If
$|X + X| \le \kappa |X|$, the model group can be taken of size at most $\kappa^{2s} |X|$. The
image of $X_1$ then has density at least $(s \kappa^{2s})^{-1}$ in $\mathbb{Z}/m\mathbb{Z}$, a
bound independent of $q$. -/
lemma exists_ruzsa_model_of_doubling {q s : ℕ} {κ : ℝ} (hq : q.Prime) (hs : 0 < s)
    {X : Finset (ZMod q)} (hX : X.Nonempty) (hXX : ((X + X).card : ℝ) ≤ κ * X.card) :
    ∃ (m : ℕ) (X₁ : Finset (ZMod q)) (φ : ZMod q → ZMod m),
      0 < m ∧ (m : ℝ) ≤ κ ^ (2 * s) * X.card ∧ X₁ ⊆ X ∧ X.card ≤ s * X₁.card ∧
      IsAddFreimanIso s (X₁ : Set (ZMod q)) (X₁.image φ : Set (ZMod m)) φ := by
  obtain ⟨X₁, hX₁, hcard, φ, hφ⟩ := exists_ruzsa_model hq hs hX (le_refl (s • X - s • X).card)
  refine ⟨(s • X - s • X).card, X₁, φ,
    Finset.card_pos.2 ⟨0, zero_mem_nsmul_sub_nsmul hX s⟩, ?_, hX₁, hcard, hφ⟩
  have hbound : ((s • X - s • X).card : ℝ)
      ≤ (((X + X).card : ℝ) / X.card) ^ (s + s) * X.card := by
    have hcast := (NNRat.cast_le (K := ℝ)).2
      (Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hX X s s)
    push_cast [NNRat.cast_pow] at hcast
    exact hcast
  apply le_trans hbound
  rw [two_mul]
  gcongr
  exact (div_le_iff₀ (Nat.cast_pos.2 hX.card_pos)).2 hXX

end

end ChangFreimanRuzsa
