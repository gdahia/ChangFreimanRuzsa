/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.Properization.AlgebraAndGAPBasics
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-!
# Short relations and iterated properization

Let $P$ be a GAP of dimension $d$ in an abelian group in which the multiples $n a$, $n < N$, of
every nonzero $a$ are distinct, with $N$ large compared with $|P|$. The short relations of $P$ are
the relations among its steps in the $3$-dilate of its coefficient box. Their saturated span
consists of relations, and dividing the coefficient lattice by it and reboxing the quotient gives a
GAP of smaller dimension containing $P$, unless $P$ has no short relation, in which case $P$ is
2-proper.
Iterating proves that $P$ lies in a 2-proper GAP of dimension at most $d$ and of size at most
$e^{14 (d + 2)^4} |P|$.

## Main statements

* `GAP.twoProper_or_exists_GAP_dim_lt`: one step of the iteration.
* `exists_twoProperGAP_container_of_injOn_nsmul`: the iterated statement.
* `exists_twoProperGAP_container` and `exists_twoProperGAP_container_of_isAddTorsionFree`: the
  statements in $\mathbb{Z}/q\mathbb{Z}$ for prime $q$ and in torsion-free groups.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open scoped Pointwise Topology

noncomputable section

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

namespace GAP

/-- The half-widths of the coefficient box of `P`. The relations of `P` inside its coefficient box
are exactly the points of `GAP.relations P` in the integer box of these half-widths. -/
def halfWidth (P : GAP G) (i : Fin P.dim) : ℕ := P.length i - 1

lemma halfWidth_pos {P : GAP G} (hlen : ∀ i, 2 ≤ P.length i) (i : Fin P.dim) :
    0 < P.halfWidth i := by
  rw [halfWidth]
  grind [hlen i]

lemma cast_halfWidth (P : GAP G) (i : Fin P.dim) :
    ((P.halfWidth i : ℕ) : ℝ) = (P.length i : ℝ) - 1 := by
  rw [halfWidth, Nat.cast_sub (P.length_pos i), Nat.cast_one]

/-! ### The rank of the short relations

The relation lattice of a progression in $\mathbb{Z}/q\mathbb{Z}$ has full rank, since it contains
$q \mathbb{Z}^d$, but that of a progression in $\mathbb{Z}$ does not. The rank reduction therefore
does not use the successive minima of the relation lattice. It uses the largest number of linearly
independent relations in a fixed dilate of the coefficient box, which is defined in every group. -/

open Classical in
/-- The largest `k ≤ dim` such that the `t`-dilate of the coefficient box of `P` contains `k`
linearly independent relations of `P`. -/
def shortRelationRank (P : GAP G) (t : ℝ) : ℕ :=
  Nat.findGreatest (fun k ↦ HasIndependentShort P.relations P.halfWidth k t) P.dim

open Classical in
lemma shortRelationRank_le_dim (P : GAP G) (t : ℝ) :
    P.shortRelationRank t ≤ P.dim :=
  Nat.findGreatest_le _

open Classical in
/-- A family of `k ≤ dim` independent relations inside the cutoff dilate bounds the short rank
from below. -/
lemma le_shortRelationRank (P : GAP G) {k : ℕ} {t : ℝ} (hk : k ≤ P.dim)
    (h : HasIndependentShort P.relations P.halfWidth k t) : k ≤ P.shortRelationRank t :=
  Nat.le_findGreatest hk h

open Classical in
/-- The short rank is attained by that many independent relations inside the cutoff dilate. -/
lemma hasIndependentShort_shortRelationRank (P : GAP G) (t : ℝ) :
    HasIndependentShort P.relations P.halfWidth (P.shortRelationRank t) t :=
  Nat.findGreatest_spec (P := fun k ↦ HasIndependentShort P.relations P.halfWidth k t)
    (Nat.zero_le _) ⟨Fin.elim0, linearIndependent_empty_type, fun j ↦ j.elim0⟩

/-- A maximal independent family $v$ of relations in the $t$-dilate of the coefficient box, together
with a Smith normal form of the saturated span of $v$ whose rank is `shortRelationRank`. -/
lemma exists_smithNormalForm_shortRelations (P : GAP G) (t : ℝ) :
    ∃ (v : Fin (P.shortRelationRank t) → (Fin P.dim → ℤ))
      (S : Finset (Fin P.dim → ℤ))
      (_snf : Module.Basis.SmithNormalForm
        (saturatedSpan S) (Fin P.dim) (P.shortRelationRank t)),
      S = Finset.univ.image v ∧
        LinearIndependent ℤ v ∧
          (∀ j, v j ∈ P.relations) ∧ ∀ j, IsShort P.halfWidth t (v j) := by
  obtain ⟨v, hindep, hv⟩ := P.hasIndependentShort_shortRelationRank t
  set S : Finset (Fin P.dim → ℤ) := Finset.univ.image v with hS
  obtain ⟨n, snf⟩ := (saturatedSpan S).smithNormalForm (Pi.basisFun ℤ (Fin P.dim))
  have hrank : Module.finrank ℤ (saturatedSpan S) = P.shortRelationRank t := by
    rw [finrank_saturatedSpan, hS, finrank_integerGeneratedSubspace_image v hindep]
  rw [Module.finrank_eq_card_basis snf.bN, Fintype.card_fin] at hrank
  subst n
  refine ⟨v, S, snf, hS, hindep, ?_, ?_⟩
  · intro j
    obtain ⟨hrel, -⟩ := hv j
    exact hrel
  · intro j
    obtain ⟨-, hshort⟩ := hv j
    exact hshort

/-- A maximal independent family below the cutoff spans every relation below that cutoff. -/
lemma mem_saturatedSpan_shortRelations (P : GAP G)
    {r : ℕ} (hr : r = P.shortRelationRank 3)
    (v : Fin r → (Fin P.dim → ℤ))
    (hindep : LinearIndependent ℤ v)
    (hvrel : ∀ j, v j ∈ P.relations)
    (hvshort : ∀ j, IsShort P.halfWidth 3 (v j))
    {w : Fin P.dim → ℤ} (hwrel : w ∈ P.relations)
    (hwshort : IsShort P.halfWidth 3 w) :
    w ∈ saturatedSpan (Finset.univ.image v) := by
  by_contra hwspan
  have hvR : LinearIndependent ℝ (fun j ↦ intVectorToReal (v j)) :=
    (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℝ) (ι' := Fin P.dim)).mpr hindep
  have hwR : intVectorToReal w ∉
      Submodule.span ℝ (Set.range fun j ↦ intVectorToReal (v j)) := by
    intro hw
    apply hwspan
    change intVectorToReal w ∈
      Submodule.span ℝ
        (intVectorToReal '' (↑(Finset.univ.image v) : Set (Fin P.dim → ℤ)))
    have hset :
        intVectorToReal '' (↑(Finset.univ.image v) : Set (Fin P.dim → ℤ)) =
          Set.range fun j ↦ intVectorToReal (v j) := by
      ext
      simp
    rwa [hset]
  have hcons : LinearIndependent ℤ (Fin.cons w v) := by
    apply (linearIndependent_algebraMap_comp_iff
      (R := ℤ) (S := ℝ) (ι' := Fin P.dim)).mp
    have heq :
        (fun i : Fin (r + 1) ↦
          algebraMap ℤ ℝ ∘
            (Fin.cons w v : Fin (r + 1) → (Fin P.dim → ℤ)) i) =
          Fin.cons (intVectorToReal w) (fun j ↦ intVectorToReal (v j)) := by
      funext i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro j
        rfl
    rw [heq]
    exact linearIndependent_finCons.mpr ⟨hvR, hwR⟩
  have hrd : r < P.dim := by
    have hcard := hcons.fintype_card_le_finrank
    rw [Module.finrank_fin_fun] at hcard
    simp only [Fintype.card_fin] at hcard
    grind
  have hfamily : HasIndependentShort P.relations P.halfWidth (r + 1) 3 := by
    refine ⟨Fin.cons w v, hcons, ?_⟩
    apply Fin.cases
    · exact ⟨hwrel, hwshort⟩
    · intro j
      exact ⟨hvrel j, hvshort j⟩
  grind [P.le_shortRelationRank (Nat.succ_le_of_lt hrd) hfamily]

/-- Multiples of a nonzero element of a prime cyclic group are distinct below the modulus. -/
lemma injOn_nsmul_of_prime {q : ℕ} (hq : Nat.Prime q) {a : ZMod q} (ha : a ≠ 0) :
    Set.InjOn (fun n : ℕ ↦ n • a) (Set.Iio q) := by
  have : Fact q.Prime := ⟨hq⟩
  intro m hm n hn h
  simp only [nsmul_eq_mul] at h
  rw [← ZMod.val_cast_of_lt hm, ← ZMod.val_cast_of_lt hn, mul_right_cancel₀ ha h]

omit [DecidableEq G] in
/-- Multiples of a nonzero element of a torsion-free group are distinct. -/
lemma injOn_nsmul_of_isAddTorsionFree [IsAddTorsionFree G] (N : ℕ) {a : G} (ha : a ≠ 0) :
    Set.InjOn (fun n : ℕ ↦ n • a) (Set.Iio N) := by
  intro m _ n _ h
  have h' : ((m : ℤ) - n) • a = 0 := by
    rwa [sub_smul, natCast_zsmul, natCast_zsmul, sub_eq_zero]
  exact_mod_cast sub_eq_zero.1 ((IsAddTorsionFree.zsmul_eq_zero_iff_left ha).1 h')

/-- Suppose that the multiples $n a$, $n < N$, of every nonzero $a$ are distinct, as in a cyclic
group of prime order $N$ or in a torsion-free group, and that $(6d + 1)^d |P| < N$. Then the
saturated span of a family of relations of $P$ in the $3$-dilate of its coefficient box consists of
relations. Otherwise the first $N$ multiples of a vector in the span that is not a relation, reduced
modulo the family, would give $N$ distinct elements in a bounded dilate of $P$. -/
lemma saturatedSpan_shortRelations_le_relations {N r : ℕ} (P : GAP G)
    (hG : ∀ a : G, a ≠ 0 → Set.InjOn (fun n : ℕ ↦ n • a) (Set.Iio N))
    (v : Fin r → (Fin P.dim → ℤ))
    (hrel : ∀ j, v j ∈ P.relations)
    (hshort : ∀ j, IsShort P.halfWidth 3 (v j)) (hrd : r ≤ P.dim)
    (hroom : (2 * (3 * P.dim) + 1) ^ P.dim * P.carrier.card < N) :
    (saturatedSpan (Finset.univ.image v)).toAddSubgroup ≤ P.relations := by
  intro x hx
  change stepHom P x = 0
  by_contra hxne
  have hspanrel :
      Submodule.span ℤ (Set.range v) ≤
        AddSubgroup.toIntSubmodule P.relations := by
    apply Submodule.span_le.mpr
    rintro w ⟨j, rfl⟩
    exact hrel j
  have hreduce : ∀ a : Fin N, ∃ y : Fin P.dim → ℤ,
      stepHom P y = (a : ℕ) • stepHom P x ∧
        y ∈ intBox (fun i ↦ 3 * P.dim * P.halfWidth i) := by
    intro a
    obtain ⟨y, hcongr, hy⟩ := exists_congr_span_isShort v hshort
      (x := (a : ℤ) • x) (Submodule.smul_mem _ _ hx)
    refine ⟨y, ?_, ?_⟩
    · have hzero : stepHom P ((a : ℤ) • x - y) = 0 := hspanrel hcongr
      rw [map_sub, sub_eq_zero, map_zsmul] at hzero
      rw [← hzero]
      exact natCast_zsmul (stepHom P x) a
    · rw [mem_intBox]
      intro i
      have hrdR : (r : ℝ) ≤ P.dim := by exact_mod_cast hrd
      have hyr : |(y i : ℝ)| ≤ (3 * P.dim * P.halfWidth i : ℕ) := by
        push_cast
        nlinarith [hy i, mul_le_mul_of_nonneg_right hrdR
          (by positivity : (0 : ℝ) ≤ 3 * P.halfWidth i)]
      rw [← Int.cast_abs] at hyr
      exact_mod_cast hyr
  choose y hstep hbox using hreduce
  let f : Fin N → P.boundedStepImage (3 * P.dim) :=
    fun a ↦ ⟨stepHom P (y a), Finset.mem_image.mpr ⟨y a, hbox a, rfl⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hmap : (a : ℕ) • stepHom P x = (b : ℕ) • stepHom P x := by
      rw [← hstep a, ← hstep b]
      exact congr_arg Subtype.val hab
    exact Fin.ext (hG _ hxne a.isLt b.isLt hmap)
  have hcard : N ≤ (P.boundedStepImage (3 * P.dim)).card := by
    simpa using Fintype.card_le_of_injective f hf
  exact (not_lt_of_ge (hcard.trans (P.card_boundedStepImage_le (3 * P.dim)))) hroom

/-! ### Properness through the short rank -/

/-- A progression with all lengths $\ell_i \ge 2$ and no nonzero relation in the $3$-dilate of its
coefficient box is 2-proper. Indeed a relation $v$ in the doubled box has
$|v_i| \le 2 \ell_i - 1 \le 3 (\ell_i - 1)$. -/
lemma twoProper_of_shortRelationRank_eq_zero (P : GAP G) (hlen : ∀ i, 2 ≤ P.length i)
    (hrank : P.shortRelationRank 3 = 0) : P.TwoProper := by
  apply P.twoProper_iff.mpr
  intro v hv hlt
  by_contra hne
  obtain ⟨i₀, -⟩ := Function.ne_iff.1 hne
  have hshort : IsShort P.halfWidth 3 v := by
    intro i
    have hlen' : (2 : ℤ) ≤ P.length i := by exact_mod_cast hlen i
    have hint : |v i| ≤ 3 * ((P.length i : ℤ) - 1) := by
      linarith [Int.lt_iff_add_one_le.mp (hlt i)]
    rw [← Int.cast_abs, P.cast_halfWidth]
    exact_mod_cast hint
  have := P.le_shortRelationRank (t := 3) (Nat.succ_le_of_lt i₀.pos)
    ⟨fun _ ↦ v, linearIndependent_unique_iff.mpr hne, fun _ ↦ ⟨hv, hshort⟩⟩
  grind

/-! ### Projecting by a saturated family -/

/-- The image of the coefficient box after quotienting by a saturated span in Smith
coordinates. -/
def smithQuotientBody (P : GAP G) {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    Set (Fin (P.dim - n) → ℝ) :=
  smithRealQuotientMap snf '' BoxLattice.realBox P.halfWidth

lemma isCompact_smithQuotientBody (P : GAP G) {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    IsCompact (P.smithQuotientBody snf) := by
  apply (Metric.isCompact_of_isClosed_isBounded (BoxLattice.isClosed_realBox P.halfWidth)
    (BoxLattice.isBounded_realBox P.halfWidth)).image
  exact LinearMap.continuous_of_finiteDimensional (smithRealQuotientMap snf)

lemma isBounded_smithQuotientBody (P : GAP G) {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    Bornology.IsBounded (P.smithQuotientBody snf) :=
  (P.isCompact_smithQuotientBody snf).isBounded

/-- The integer lattice points of a saturated projected coefficient body. -/
def smithQuotientIntegerPoints (P : GAP G) {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    Set (Fin (P.dim - n) → ℤ) :=
  {v | BoxLattice.intCastHom v ∈ P.smithQuotientBody snf}

lemma smithQuotientIntegerPoints_finite (P : GAP G) {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    (P.smithQuotientIntegerPoints snf).Finite := by
  let L : AddSubgroup (Fin (P.dim - n) → ℝ) :=
    (⊤ : AddSubgroup (Fin (P.dim - n) → ℤ)).map BoxLattice.intCastHom
  let : DiscreteTopology L := BoxLattice.discreteTopology_map ⊤
  have hinter : (P.smithQuotientBody snf ∩
      (L : Set (Fin (P.dim - n) → ℝ))).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      (P.isBounded_smithQuotientBody snf) AddSubgroup.isClosed_of_discreteTopology
  refine Set.Finite.of_finite_image (f := BoxLattice.intCastHom) ?_
    BoxLattice.intCastHom_injective.injOn
  apply hinter.subset
  rintro x ⟨v, hv, rfl⟩
  refine ⟨hv, AddSubgroup.mem_map.mpr ⟨v, Set.mem_univ v, rfl⟩⟩

/-- The finite set of integer points of a saturated projected coefficient body. -/
noncomputable def smithQuotientCoords (P : GAP G) {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    Finset (Fin (P.dim - n) → ℤ) :=
  (P.smithQuotientIntegerPoints_finite snf).toFinset

lemma mem_smithQuotientCoords {P : GAP G} {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    {snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n}
    {v : Fin (P.dim - n) → ℤ} :
    v ∈ P.smithQuotientCoords snf ↔
      BoxLattice.intCastHom v ∈ P.smithQuotientBody snf := by
  rw [smithQuotientCoords, Set.Finite.mem_toFinset]
  rfl

/-- The integer points of the projected coefficient box lie in a proper GAP of dimension
$d - n$ with at most `boxReboxingFactor (P.dim - n)` times as many elements. -/
lemma exists_proper_GAP_reboxing_smithQuotientCoords
    (P : GAP G) (hlen : ∀ i, 2 ≤ P.length i) {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    ∃ Q : GAP (Fin (P.dim - n) → ℤ), Q.Proper ∧
      P.smithQuotientCoords snf ⊆ Q.carrier ∧ Q.dim = P.dim - n ∧
      Q.carrier.card ≤ boxReboxingFactor (P.dim - n) *
        (P.smithQuotientCoords snf).card := by
  apply exists_proper_GAP_reboxing_image_realBox P.halfWidth
    (fun i ↦ P.halfWidth_pos hlen i) (smithRealQuotientMap snf)
    (smithQuotientMap snf) (smithRealQuotientMap_intCast snf)
    (smithRealQuotientMap_surjective snf) (P.smithQuotientCoords snf)
  intro v
  rw [mem_smithQuotientCoords]
  rfl

/-- Original coefficient vectors map to integer points of the saturated projected body. -/
lemma smithQuotientMap_mem_smithQuotientCoords {P : GAP G} {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    {snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n}
    {v : Fin P.dim → ℤ} (hv : v ∈ symBox P) :
    smithQuotientMap snf v ∈ P.smithQuotientCoords snf := by
  rw [mem_smithQuotientCoords, ← smithRealQuotientMap_intCast]
  refine ⟨BoxLattice.intCastHom v, ?_, rfl⟩
  intro i
  have hi := mem_symBox.mp hv i
  have hvi : |v i| ≤ (P.halfWidth i : ℤ) := by
    rw [halfWidth]
    grind [P.length_pos i]
  rw [BoxLattice.intCastHom_apply, ← Int.cast_abs]
  exact_mod_cast hvi

/-- Every lattice point of the projected body has an integral lift in a controlled dilate of the
original coefficient box when the quotient directions are `3`-short. -/
lemma exists_bounded_lift_smithQuotientCoords {P : GAP G} {r : ℕ}
    (v : Fin r → (Fin P.dim → ℤ)) {S : Finset (Fin P.dim → ℤ)}
    (hS : S = Finset.univ.image v)
    (hshort : ∀ j, IsShort P.halfWidth 3 (v j))
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) r)
    {y : Fin (P.dim - r) → ℤ} (hy : y ∈ P.smithQuotientCoords snf) :
    ∃ z : Fin P.dim → ℤ, smithQuotientMap snf z = y ∧
      z ∈ intBox (fun i ↦ (3 * r + 1) * P.halfWidth i) := by
  rw [mem_smithQuotientCoords] at hy
  obtain ⟨b, hb, hby⟩ := hy
  set z₀ := smithQuotientLift snf y with hz₀
  have hker : BoxLattice.intCastHom z₀ - b ∈ integerGeneratedSubspace S := by
    rw [← smithRealQuotientMap_eq_zero_iff snf, map_sub,
      smithRealQuotientMap_intCast, smithQuotientMap_lift]
    exact sub_eq_zero.mpr hby.symm
  have hspan : intVectorToReal z₀ - b ∈
      Submodule.span ℝ (Set.range fun j ↦ intVectorToReal (v j)) := by
    rw [hS, integerGeneratedSubspace] at hker
    have hset :
        intVectorToReal '' (↑(Finset.univ.image v) : Set (Fin P.dim → ℤ)) =
          Set.range fun j ↦ intVectorToReal (v j) := by
      ext
      simp
    rwa [hset] at hker
  obtain ⟨z, hcongr, hz⟩ := exists_congr_close_isShort v hshort z₀ b hspan
  refine ⟨z, ?_, ?_⟩
  · have hspanSat : Submodule.span ℤ (Set.range v) ≤ saturatedSpan S := by
      apply Submodule.span_le.mpr
      rintro w ⟨j, rfl⟩
      apply subset_saturatedSpan S
      simp [hS]
    have hmaps := (smithQuotientMap_eq_iff snf z₀ z).mpr (hspanSat hcongr)
    rw [smithQuotientMap_lift] at hmaps
    exact hmaps.symm
  · rw [mem_intBox]
    intro i
    have hb' : |b i| ≤ (P.halfWidth i : ℝ) := hb i
    have hreal : |(z i : ℝ)| ≤ ((3 * r + 1) * P.halfWidth i : ℕ) := by
      push_cast
      nlinarith [hz i, Nat.cast_nonneg (α := ℝ) (P.halfWidth i)]
    rw [← Int.cast_abs] at hreal
    exact_mod_cast hreal

/-- The image in the ambient group of the projected body's lattice points is controlled by a
bounded dilate of the original progression. -/
lemma card_image_smithQuotientCoords_le {P : GAP G} {r : ℕ}
    (v : Fin r → (Fin P.dim → ℤ)) {S : Finset (Fin P.dim → ℤ)}
    (hS : S = Finset.univ.image v)
    (hshort : ∀ j, IsShort P.halfWidth 3 (v j))
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) r)
    (hrel : (saturatedSpan S).toAddSubgroup ≤ P.relations) :
    ((P.smithQuotientCoords snf).image
      (stepsHom (P.smithQuotientStep snf))).card ≤
        (2 * (3 * r + 1) + 1) ^ P.dim * P.carrier.card := by
  refine (Finset.card_le_card ?_).trans (P.card_boundedStepImage_le (3 * r + 1))
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨z, hzmap, hz⟩ :=
    P.exists_bounded_lift_smithQuotientCoords v hS hshort snf hy
  rw [boundedStepImage, Finset.mem_image]
  refine ⟨z, hz, ?_⟩
  rw [← P.stepHom_smithQuotientMap snf hrel z, hzmap]

/-- Two projected lattice points with the same group image differ by a relation that admits a
controlled representative modulo the saturated quotient directions. -/
lemma exists_bounded_relation_of_same_smithImage {P : GAP G} {r : ℕ}
    (v : Fin r → (Fin P.dim → ℤ)) {S : Finset (Fin P.dim → ℤ)}
    (hS : S = Finset.univ.image v)
    (hshort : ∀ j, IsShort P.halfWidth 3 (v j))
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) r)
    (hrel : (saturatedSpan S).toAddSubgroup ≤ P.relations)
    {y y₀ : Fin (P.dim - r) → ℤ}
    (hy : y ∈ P.smithQuotientCoords snf) (hy₀ : y₀ ∈ P.smithQuotientCoords snf)
    (himage : stepsHom (P.smithQuotientStep snf) y =
      stepsHom (P.smithQuotientStep snf) y₀) :
    ∃ z ∈ P.relations, smithQuotientMap snf z = y - y₀ ∧
      z ∈ intBox (fun i ↦ (3 * r + 2) * P.halfWidth i) := by
  rw [mem_smithQuotientCoords] at hy hy₀
  obtain ⟨b, hb, hby⟩ := hy
  obtain ⟨b₀, hb₀, hb₀y⟩ := hy₀
  set z₀ := smithQuotientLift snf (y - y₀) with hz₀
  have hker : BoxLattice.intCastHom z₀ - (b - b₀) ∈ integerGeneratedSubspace S := by
    rw [← smithRealQuotientMap_eq_zero_iff snf, map_sub,
      smithRealQuotientMap_intCast, smithQuotientMap_lift, map_sub, map_sub]
    rw [hby, hb₀y]
    exact sub_self _
  have hspan : intVectorToReal z₀ - (b - b₀) ∈
      Submodule.span ℝ (Set.range fun j ↦ intVectorToReal (v j)) := by
    rw [hS, integerGeneratedSubspace] at hker
    have hset :
        intVectorToReal '' (↑(Finset.univ.image v) : Set (Fin P.dim → ℤ)) =
          Set.range fun j ↦ intVectorToReal (v j) := by
      ext
      simp
    rwa [hset] at hker
  obtain ⟨z, hcongr, hz⟩ :=
    exists_congr_close_isShort v hshort z₀ (b - b₀) hspan
  have hspanSat : Submodule.span ℤ (Set.range v) ≤ saturatedSpan S := by
    apply Submodule.span_le.mpr
    rintro w ⟨j, rfl⟩
    apply subset_saturatedSpan S
    simp [hS]
  have hzmap : smithQuotientMap snf z = y - y₀ := by
    have hmaps := (smithQuotientMap_eq_iff snf z₀ z).mpr (hspanSat hcongr)
    rw [smithQuotientMap_lift] at hmaps
    exact hmaps.symm
  refine ⟨z, ?_, hzmap, ?_⟩
  · change stepHom P z = 0
    rw [← P.stepHom_smithQuotientMap snf hrel z, hzmap, map_sub, himage, sub_self]
  · rw [mem_intBox]
    intro i
    have hb' : |b i| ≤ (P.halfWidth i : ℝ) := hb i
    have hb₀' : |b₀ i| ≤ (P.halfWidth i : ℝ) := hb₀ i
    have hbb₀ : |(b - b₀) i| ≤ 2 * (P.halfWidth i : ℝ) :=
      (abs_sub _ _).trans (by linarith)
    have hreal : |(z i : ℝ)| ≤ ((3 * r + 2) * P.halfWidth i : ℕ) := by
      push_cast
      nlinarith [hz i, Nat.cast_nonneg (α := ℝ) (P.halfWidth i)]
    rw [← Int.cast_abs] at hreal
    exact_mod_cast hreal

/-- Each fibre of the quotient step map on the projected lattice points has at most
$(2r + 4)^d$ elements. Distinct points of a fibre lift to relations separated by the $3$-dilate of
the coefficient box, since every relation in that dilate lies in the saturated span of the short
relations. -/
lemma card_smithQuotientCoords_fiber_le (P : GAP G)
    {r : ℕ} (hr : r = P.shortRelationRank 3)
    (v : Fin r → (Fin P.dim → ℤ)) (hindep : LinearIndependent ℤ v)
    (hvrel : ∀ j, v j ∈ P.relations)
    (hvshort : ∀ j, IsShort P.halfWidth 3 (v j))
    {S : Finset (Fin P.dim → ℤ)} (hS : S = Finset.univ.image v)
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) r)
    (hrel : (saturatedSpan S).toAddSubgroup ≤ P.relations)
    (g : G) :
    ((P.smithQuotientCoords snf).filter fun y ↦
      stepsHom (P.smithQuotientStep snf) y = g).card ≤
        (2 * r + 4) ^ P.dim := by
  classical
  set F := (P.smithQuotientCoords snf).filter fun y ↦
    stepsHom (P.smithQuotientStep snf) y = g with hF
  rcases Finset.eq_empty_or_nonempty F with hFempty | ⟨y₀, hy₀F⟩
  · rw [hFempty, Finset.card_empty]
    positivity
  obtain ⟨hy₀, hy₀g⟩ := Finset.mem_filter.mp (hF ▸ hy₀F)
  have hlift : ∀ y, ∃ z : Fin P.dim → ℤ, y ∈ F →
      z ∈ P.relations ∧ smithQuotientMap snf z = y - y₀ ∧
        z ∈ intBox (fun i ↦ (3 * r + 2) * P.halfWidth i) := by
    intro y
    by_cases hyF : y ∈ F
    · obtain ⟨hy, hyg⟩ := Finset.mem_filter.mp (hF ▸ hyF)
      obtain ⟨z, hzrel, hzmap, hzbox⟩ :=
        P.exists_bounded_relation_of_same_smithImage v hS hvshort snf hrel hy hy₀
          (hyg.trans hy₀g.symm)
      exact ⟨z, fun _ ↦ ⟨hzrel, hzmap, hzbox⟩⟩
    · exact ⟨0, fun h ↦ absurd h hyF⟩
  choose z hzrel hzmap hzbox using hlift
  have hzinj : Set.InjOn z F := by
    intro a ha b hb hab
    have hmaps := congr_arg (smithQuotientMap snf) hab
    rwa [hzmap a ha, hzmap b hb, sub_left_inj] at hmaps
  set Z := F.image z with hZ
  have hZcard : Z.card = F.card := by
    rw [hZ, Finset.card_image_of_injOn hzinj]
  have hbox : ∀ u ∈ Z, ∀ i,
      |u i| ≤ (((3 * r + 2) * P.halfWidth i : ℕ) : ℤ) := by
    intro u hu i
    rw [hZ, Finset.mem_image] at hu
    obtain ⟨y, hyF, rfl⟩ := hu
    exact mem_intBox.mp (hzbox y hyF) i
  have hsep : ∀ u ∈ Z, ∀ w ∈ Z, u ≠ w →
      ∃ i, ((3 * P.halfWidth i : ℕ) : ℤ) < |u i - w i| := by
    intro u hu w hw huw
    rw [hZ, Finset.mem_image] at hu hw
    obtain ⟨a, haF, rfl⟩ := hu
    obtain ⟨b, hbF, rfl⟩ := hw
    by_contra! hcon
    have hdiffrel : z a - z b ∈ P.relations :=
      P.relations.sub_mem (hzrel a haF) (hzrel b hbF)
    have hdiffshort : IsShort P.halfWidth 3 (z a - z b) := by
      intro i
      have hi := hcon i
      push_cast at hi
      rw [Pi.sub_apply, ← Int.cast_abs]
      exact_mod_cast hi
    have hdiffSat : z a - z b ∈ saturatedSpan S := by
      rw [hS]
      exact P.mem_saturatedSpan_shortRelations hr v hindep hvrel hvshort
        hdiffrel hdiffshort
    have hmaps := (smithQuotientMap_eq_iff snf (z a) (z b)).mpr hdiffSat
    rw [hzmap a haF, hzmap b hbF, sub_left_inj] at hmaps
    exact huw (congr_arg z hmaps)
  have hpack := card_mul_prod_le_of_separated hbox hsep
  have hfactor : ∏ i : Fin P.dim,
      (2 * (((3 * r + 2) * P.halfWidth i) + 3 * P.halfWidth i) + 1) ≤
        (2 * r + 4) ^ P.dim * ∏ i : Fin P.dim, (3 * P.halfWidth i + 1) := by
    refine (Finset.prod_le_prod (g := fun i ↦
      (2 * r + 4) * (3 * P.halfWidth i + 1)) ?_).trans ?_
    · intro i _
      nlinarith [Nat.zero_le (P.halfWidth i)]
    · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
  have hmul : F.card * ∏ i : Fin P.dim, (3 * P.halfWidth i + 1) ≤
      (2 * r + 4) ^ P.dim * ∏ i : Fin P.dim, (3 * P.halfWidth i + 1) := by
    rw [← hZcard]
    exact hpack.trans hfactor
  have hden : 0 < ∏ i : Fin P.dim, (3 * P.halfWidth i + 1) := by positivity
  exact (Nat.mul_le_mul_right_iff hden).mp hmul

/-- The projected lattice points number at most $((2r + 4)(2(3r + 1) + 1))^d |P|$, by the bound
on their image in the group and the bound on each fibre. -/
lemma card_smithQuotientCoords_le (P : GAP G)
    {r : ℕ} (hr : r = P.shortRelationRank 3)
    (v : Fin r → (Fin P.dim → ℤ)) (hindep : LinearIndependent ℤ v)
    (hvrel : ∀ j, v j ∈ P.relations)
    (hvshort : ∀ j, IsShort P.halfWidth 3 (v j))
    {S : Finset (Fin P.dim → ℤ)} (hS : S = Finset.univ.image v)
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) r)
    (hrel : (saturatedSpan S).toAddSubgroup ≤ P.relations) :
    (P.smithQuotientCoords snf).card ≤
      ((2 * r + 4) * (2 * (3 * r + 1) + 1)) ^ P.dim * P.carrier.card := by
  let φ := stepsHom (P.smithQuotientStep snf)
  have hcard : (P.smithQuotientCoords snf).card ≤
      (2 * r + 4) ^ P.dim *
        ((P.smithQuotientCoords snf).image φ).card := by
    apply Finset.card_le_mul_card_image_of_maps_to
      (f := φ) (fun y hy ↦ Finset.mem_image_of_mem _ hy) _
    intro g _
    exact P.card_smithQuotientCoords_fiber_le hr v hindep hvrel hvshort
      hS snf hrel g
  apply hcard.trans
  apply (Nat.mul_le_mul_left ((2 * r + 4) ^ P.dim)
    (P.card_image_smithQuotientCoords_le v hS hvshort snf hrel)).trans
  rw [← mul_assoc, ← mul_pow]

/-- If the saturated span of $S$ consists of relations and has rank $n$, then $P$ lies in a GAP of
dimension at most $d - n$ whose size is at most `boxReboxingFactor (P.dim - n)` times the number of
projected lattice points. -/
lemma exists_container_of_saturated_relations (P : GAP G) {n : ℕ}
    {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n)
    (hlen : ∀ i, 2 ≤ P.length i)
    (hrel : (saturatedSpan S).toAddSubgroup ≤ P.relations) :
    ∃ Q : GAP G, P.carrier ⊆ Q.carrier ∧ Q.dim ≤ P.dim - n ∧
      (Q.carrier.card : ℝ) ≤
        boxReboxingFactor (P.dim - n) *
          (P.smithQuotientCoords snf).card := by
  obtain ⟨P', -, hDP', hP'dim, hP'card⟩ :=
    P.exists_proper_GAP_reboxing_smithQuotientCoords hlen snf
  set Q : GAP G :=
    (P'.map (stepsHom (P.smithQuotientStep snf))).shift P.origin with hQ
  have hsub : P.carrier ⊆ Q.carrier := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := P.mem_carrier_iff_exists_intCoeffs.mp hx
    have hcsym : c ∈ symBox P := by
      rw [mem_symBox]
      intro i
      obtain ⟨h0, hlt⟩ := hc i
      rwa [abs_of_nonneg h0]
    have hcP' : smithQuotientMap snf c ∈ P'.carrier :=
      hDP' (smithQuotientMap_mem_smithQuotientCoords hcsym)
    have hcmap : stepsHom (P.smithQuotientStep snf) (smithQuotientMap snf c) ∈
        (P'.map (stepsHom (P.smithQuotientStep snf))).carrier :=
      Finset.mem_image_of_mem _ hcP'
    refine Finset.mem_image.mpr
      ⟨stepsHom (P.smithQuotientStep snf) (smithQuotientMap snf c), hcmap, ?_⟩
    rw [P.stepHom_smithQuotientMap snf hrel]
    change stepHom P c + P.origin = P.origin + stepHom P c
    abel
  refine ⟨Q, hsub, hP'dim.le, ?_⟩
  have hQcard : Q.carrier.card ≤ P'.carrier.card :=
    Finset.card_image_le.trans (P'.card_map_le (stepsHom (P.smithQuotientStep snf)))
  exact ((Nat.cast_le (α := ℝ)).mpr hQcard).trans (by exact_mod_cast hP'card)

/-- One step of properization. Either $P$ is 2-proper, or dividing by the saturated span of its
short relations, which consists of relations by the hypothesis on $N$, and reboxing gives a GAP of
smaller dimension containing $P$, of the size bounded by `card_smithQuotientCoords_le`. -/
lemma twoProper_or_exists_GAP_dim_lt {N : ℕ} (P : GAP G)
    (hG : ∀ a : G, a ≠ 0 → Set.InjOn (fun n : ℕ ↦ n • a) (Set.Iio N))
    (hlen : ∀ i, 2 ≤ P.length i)
    (hroom : (2 * (3 * P.dim) + 1) ^ P.dim * P.carrier.card < N) :
    P.TwoProper ∨
      ∃ Q : GAP G, P.carrier ⊆ Q.carrier ∧ Q.dim < P.dim ∧
        (Q.carrier.card : ℝ) ≤
          boxReboxingFactor (P.dim - P.shortRelationRank 3) *
            (((2 * P.shortRelationRank 3 + 4) *
                (2 * (3 * P.shortRelationRank 3 + 1) + 1)) ^ P.dim) *
              P.carrier.card := by
  by_cases hrank : P.shortRelationRank 3 = 0
  · exact Or.inl (P.twoProper_of_shortRelationRank_eq_zero hlen hrank)
  obtain ⟨v, S, snf, hS, hindep, hvrel, hvshort⟩ :=
    P.exists_smithNormalForm_shortRelations 3
  have hrd := P.shortRelationRank_le_dim 3
  have hsat : (saturatedSpan S).toAddSubgroup ≤ P.relations := by
    rw [hS]
    exact P.saturatedSpan_shortRelations_le_relations hG v hvrel hvshort hrd hroom
  obtain ⟨Q, hsub, hQdim, hQcard⟩ :=
    P.exists_container_of_saturated_relations snf hlen hsat
  refine Or.inr ⟨Q, hsub, hQdim.trans_lt (by grind), ?_⟩
  have hcoords := P.card_smithQuotientCoords_le rfl
    v hindep hvrel hvshort hS snf hsat
  have hcoordsR : ((P.smithQuotientCoords snf).card : ℝ) ≤
      (((2 * P.shortRelationRank 3 + 4) *
          (2 * (3 * P.shortRelationRank 3 + 1) + 1)) ^ P.dim : ℕ) *
        P.carrier.card := by
    exact_mod_cast hcoords
  push_cast at hcoordsR
  apply hQcard.trans
  apply (mul_le_mul_of_nonneg_left hcoordsR (by positivity)).trans_eq
  exact (mul_assoc _ _ _).symm

end GAP

/-! ## Iterated simultaneous properization -/

/-- The constant $14$ in the size bound $e^{14 (d + 2)^4} |P|$ of properization. -/
def properizationConstant : ℝ := 14

lemma properizationConstant_pos : 0 < properizationConstant := by
  norm_num [properizationConstant]

/-- Let $P$ be a GAP of dimension $d$ in an abelian group in which the multiples $n a$, $n < N$, of
every nonzero $a$ are distinct, and suppose $e^{14 (d + 2)^4} |P| \le N$. Then $P$ lies in a
2-proper GAP with all lengths at least $2$, of dimension at most $d$ and of size at most
$e^{14 (d + 2)^4} |P|$. The proof iterates `GAP.twoProper_or_exists_GAP_dim_lt`: each step costs a
factor $e^{O((d + 2)^3)}$ and lowers the dimension. -/
lemma exists_twoProperGAP_container_of_injOn_nsmul {N : ℕ} (P : GAP G)
    (hG : ∀ a : G, a ≠ 0 → Set.InjOn (fun n : ℕ ↦ n • a) (Set.Iio N))
    (hroom :
      Real.exp (properizationConstant * ((P.dim : ℝ) + 2) ^ 4) *
        P.carrier.card ≤ N) :
    ∃ Q : GAP G, Q.TwoProper ∧ P.carrier ⊆ Q.carrier ∧
      (∀ i, 1 < Q.length i) ∧ Q.dim ≤ P.dim ∧
      (Q.carrier.card : ℝ) ≤
        Real.exp (properizationConstant * ((P.dim : ℝ) + 2) ^ 4) *
          P.carrier.card := by
  induction hdimP : P.dim using Nat.strong_induction_on generalizing P with
  | h d ih =>
      let P₂ := P.scaleLengths 2 (by grind)
      have hdim : P₂.dim = d := hdimP
      have hPsub : P.carrier ⊆ P₂.carrier := by
        apply P.carrier_subset_reshape
        intro i
        grind
      have hP₂len : ∀ i, 2 ≤ P₂.length i := by
        intro i
        simp only [P₂, GAP.scaleLengths_length]
        grind [P.length_pos i]
      have hP₂cardNat : P₂.carrier.card ≤ 2 ^ d * P.carrier.card := by
        simpa [P₂, hdimP] using P.card_scaleLengths_le 2 (by grind)
      have hP₂card :
          (P₂.carrier.card : ℝ) ≤ Real.exp (((d : ℝ) + 2) ^ 3) * P.carrier.card := by
        apply (Nat.cast_le.mpr hP₂cardNat).trans
        push_cast
        exact mul_le_mul_of_nonneg_right (two_pow_le_exp d) (Nat.cast_nonneg _)
      have hstepRoom : (2 * (3 * P₂.dim) + 1) ^ P₂.dim * P₂.carrier.card < N := by
        have hfactor := saturation_room_factor_le_exp_cube d
        have hfactorCard :
            (((2 * (3 * d) + 1) ^ d * P₂.carrier.card : ℕ) : ℝ) ≤
              Real.exp (13 * ((d : ℝ) + 2) ^ 3) * P.carrier.card := by
          rw [Nat.cast_mul]
          apply (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hP₂cardNat)
            (Nat.cast_nonneg _)).trans
          rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, ← mul_assoc]
          refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
          exact_mod_cast hfactor
        have hexp :
            Real.exp (13 * ((d : ℝ) + 2) ^ 3) <
              Real.exp (properizationConstant * ((d : ℝ) + 2) ^ 4) := by
          apply Real.exp_lt_exp.mpr
          have hx : (1 : ℝ) < (d : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) d]
          have hpow : ((d : ℝ) + 2) ^ 3 < ((d : ℝ) + 2) ^ 4 := by
            rw [pow_succ]
            nlinarith [pow_pos (by positivity : (0 : ℝ) < (d : ℝ) + 2) 3]
          rw [properizationConstant]
          nlinarith [pow_pos (by positivity : (0 : ℝ) < (d : ℝ) + 2) 4]
        have hstrict :
            Real.exp (13 * ((d : ℝ) + 2) ^ 3) * P.carrier.card <
              Real.exp (properizationConstant * ((d : ℝ) + 2) ^ 4) *
                P.carrier.card :=
          mul_lt_mul_of_pos_right hexp (by exact_mod_cast P.nonempty.card_pos)
        have hreal :
            (((2 * (3 * d) + 1) ^ d * P₂.carrier.card : ℕ) : ℝ) < (N : ℝ) :=
          hfactorCard.trans_lt (hstrict.trans_le (by rwa [hdimP] at hroom))
        rw [hdim]
        exact_mod_cast hreal
      rcases P₂.twoProper_or_exists_GAP_dim_lt hG hP₂len hstepRoom with
        hproper | ⟨Q, hP₂sub, hQdim, hQcard⟩
      · refine ⟨P₂, hproper, hPsub, ?_, hdim.le, ?_⟩
        · intro i
          grind [hP₂len i]
        · refine hP₂card.trans ?_
          refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (Nat.cast_nonneg _)
          have hA1 : 1 ≤ properizationConstant := by
            norm_num [properizationConstant]
          have hpow : ((d : ℝ) + 2) ^ 3 ≤ ((d : ℝ) + 2) ^ 4 := by
            rw [pow_succ]
            nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ) + 2) 3]
          exact (le_mul_of_one_le_left (by positivity) hA1).trans
            (mul_le_mul_of_nonneg_left hpow properizationConstant_pos.le)
      · have hrank := P₂.shortRelationRank_le_dim 3
        have hfactor :=
          saturated_quotient_factor_le_exp_cube hrank
        have hQcard' :
            (Q.carrier.card : ℝ) ≤
              Real.exp (properizationConstant * ((d : ℝ) + 2) ^ 3) *
                P.carrier.card := by
          apply hQcard.trans
          have hmul := mul_le_mul hfactor hP₂card (by positivity) (by positivity)
          apply hmul.trans_eq
          rw [hdim, ← mul_assoc, ← Real.exp_add, properizationConstant]
          congr 1
          ring_nf
        have hQroom :
            Real.exp (properizationConstant * ((Q.dim : ℝ) + 2) ^ 4) *
                Q.carrier.card ≤ N := by
          apply (mul_le_mul_of_nonneg_left hQcard' (by positivity)).trans
          rw [← mul_assoc, ← Real.exp_add]
          refine (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_)
            (Nat.cast_nonneg _)).trans hroom
          simpa [hdim, hdimP] using
            cube_step_le_fourth_difference properizationConstant_pos.le hQdim
        obtain ⟨R, hRproper, hQRsub, hRlen, hRdim, hRcard⟩ :=
          ih Q.dim (by simpa [hdim] using hQdim) Q hQroom rfl
        refine ⟨R, hRproper, hPsub.trans (hP₂sub.trans hQRsub), hRlen,
          hRdim.trans (Nat.le_of_lt (by simpa [hdim] using hQdim)), ?_⟩
        apply hRcard.trans
        apply (mul_le_mul_of_nonneg_left hQcard' (by positivity)).trans
        rw [← mul_assoc, ← Real.exp_add]
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (Nat.cast_nonneg _)
        simpa [hdim, hdimP] using
          cube_step_le_fourth_difference properizationConstant_pos.le hQdim

/-- Properization in $\mathbb{Z}/q\mathbb{Z}$ for a prime $q \ge e^{14 (d + 2)^4} |P|$. -/
lemma exists_twoProperGAP_container {q : ℕ} (P : GAP (ZMod q))
    (hq : Nat.Prime q)
    (hroom :
      Real.exp (properizationConstant * ((P.dim : ℝ) + 2) ^ 4) *
        P.carrier.card ≤ q) :
    ∃ Q : GAP (ZMod q), Q.TwoProper ∧ P.carrier ⊆ Q.carrier ∧
      (∀ i, 1 < Q.length i) ∧ Q.dim ≤ P.dim ∧
      (Q.carrier.card : ℝ) ≤
        Real.exp (properizationConstant * ((P.dim : ℝ) + 2) ^ 4) *
          P.carrier.card :=
  exists_twoProperGAP_container_of_injOn_nsmul P (fun _ ha ↦ GAP.injOn_nsmul_of_prime hq ha) hroom

/-- Properization in a torsion-free group, such as $\mathbb{Z}$, with no condition on $|P|$. -/
lemma exists_twoProperGAP_container_of_isAddTorsionFree [IsAddTorsionFree G] (P : GAP G) :
    ∃ Q : GAP G, Q.TwoProper ∧ P.carrier ⊆ Q.carrier ∧
      (∀ i, 1 < Q.length i) ∧ Q.dim ≤ P.dim ∧
      (Q.carrier.card : ℝ) ≤
        Real.exp (properizationConstant * ((P.dim : ℝ) + 2) ^ 4) *
          P.carrier.card :=
  exists_twoProperGAP_container_of_injOn_nsmul P
    (fun _ ha ↦ GAP.injOn_nsmul_of_isAddTorsionFree _ ha) (Nat.le_ceil _)

end

end ChangFreimanRuzsa
