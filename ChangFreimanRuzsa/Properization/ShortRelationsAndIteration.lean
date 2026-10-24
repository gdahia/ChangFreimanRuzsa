/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.Properization.Reshape
public import ChangFreimanRuzsa.Properization.SmithQuotient
import ChangFreimanRuzsa.Properization.ExponentialBounds
import ChangFreimanRuzsa.Properization.SaturatedSpan
import Mathlib.Algebra.Field.ZMod

/-!
# Short relations and iterated properization

Let `P` be a GAP of dimension `d` in an abelian group in which the multiples `n • a` with `n < N`
of every nonzero `a` are distinct, with `N` large compared with `#P.carrier`. The short relations
of `P` are a maximal family of independent relations among its steps in the `2`-dilate of its
coefficient box. Their saturated span consists of relations. Dividing the coefficient lattice by it
and covering the image of the coefficient box by a proper progression gives a GAP of smaller
dimension containing `P`, unless `P` has no short relation, in which case `P` is `2`-proper. One
step costs a factor `exp (2 * (d + 2) ^ 2 * log (d + 2))`. Iterating proves that `P` lies in a
`2`-proper GAP of dimension at most `d` and of size at most
`exp (2 * (d + 2) ^ 3 * log (d + 2)) * #P.carrier`.

## Main definitions

* `GAP.shortRelationRank`: the largest number of independent relations in a dilate of the
  coefficient box.
* `GAP.shortRelations` and `GAP.shortRelationSpan`: a maximal family of such relations and its
  saturated span.
* `properizationExponent`: the exponent `2 * (d + 2) ^ 3 * log (d + 2)` in the size bound of
  properization.

## Main statements

* `GAP.mem_shortRelationSpan`: every relation in the dilate lies in the saturated span.
* `GAP.shortRelationSpan_le_relations`: the saturated span consists of relations.
* `GAP.proper_add_self_or_exists_gap_dim_lt`: one step of the iteration.
* `exists_twoProperGAP_carrier_subset_dim_le_card_le_of_injOn_nsmul`: the iterated statement.
* `exists_twoProperGAP_zmod_carrier_subset_dim_le_card_le` and
  `exists_twoProperGAP_carrier_subset_dim_le_card_le_of_isAddTorsionFree`: the statements in
  `ZMod q` for prime `q` and in torsion-free groups.
-/

@[expose] public section

namespace ChangFreimanRuzsa

noncomputable section

/-- An integer vector whose real coordinates satisfy `|v i| ≤ m i` lies in the integer box of
half-widths `m`. -/
lemma mem_intBox_of_abs_le {d : ℕ} {m : Fin d → ℕ} {v : Fin d → ℤ}
    (h : ∀ i, |(v i : ℝ)| ≤ m i) : v ∈ intBox m :=
  mem_intBox.mpr fun i ↦ by exact_mod_cast h i

variable {G : Type*} [AddCommGroup G]

namespace GAP

/-- The half-widths of the coefficient box of `P`. The relations of `P` inside its coefficient box
are exactly the points of `GAP.relations P` in the integer box of these half-widths. -/
def halfWidth (P : GAP G) (i : Fin P.dim) : ℕ := P.length i - 1

lemma halfWidth_pos (P : GAP G) (i : Fin P.dim) : 0 < P.halfWidth i := by
  grind [halfWidth, P.one_lt_length i]

lemma cast_halfWidth (P : GAP G) (i : Fin P.dim) :
    ((P.halfWidth i : ℕ) : ℝ) = (P.length i : ℝ) - 1 := by
  rw [halfWidth, Nat.cast_sub (P.length_pos i), Nat.cast_one]

/-- The image under the step map of an integer vector in the `m`-dilate of the coefficient box lies
in `P.boundedStepImage m`. -/
lemma stepHom_mem_boundedStepImage [DecidableEq G] {P : GAP G} {m : ℕ} {v : Fin P.dim → ℤ}
    (hv : v ∈ intBox fun i ↦ m * P.halfWidth i) : stepHom P v ∈ P.boundedStepImage m :=
  Finset.mem_image_of_mem _ hv

/-! ### The rank of the short relations

The relation lattice of a progression in `ZMod q` has full rank, since it contains `q • ℤ ^ d`,
but that of a progression in `ℤ` does not. The rank reduction therefore does not use the
successive minima of the relation lattice. It uses the largest number of linearly independent
relations in a fixed dilate of the coefficient box, which is defined in every group. -/

open Classical in
/-- The largest `k ≤ dim` such that the `t`-dilate of the coefficient box of `P` contains `k`
linearly independent relations of `P`. -/
def shortRelationRank (P : GAP G) (t : ℝ) : ℕ :=
  Nat.findGreatest (fun k ↦ HasIndependentShort P.relations P.halfWidth k t) P.dim

open Classical in
lemma shortRelationRank_le_dim (P : GAP G) (t : ℝ) : P.shortRelationRank t ≤ P.dim :=
  Nat.findGreatest_le _

open Classical in
/-- A family of `k ≤ dim` independent relations in the `t`-dilate of the coefficient box bounds the
short rank from below. -/
lemma le_shortRelationRank {P : GAP G} {k : ℕ} {t : ℝ} (hk : k ≤ P.dim)
    (h : HasIndependentShort P.relations P.halfWidth k t) : k ≤ P.shortRelationRank t :=
  Nat.le_findGreatest hk h

open Classical in
/-- The short rank is attained by that many independent relations in the `t`-dilate of the
coefficient box. -/
lemma hasIndependentShort_shortRelationRank (P : GAP G) (t : ℝ) :
    HasIndependentShort P.relations P.halfWidth (P.shortRelationRank t) t :=
  Nat.findGreatest_spec (P := fun k ↦ HasIndependentShort P.relations P.halfWidth k t)
    (Nat.zero_le _) ⟨Fin.elim0, linearIndependent_empty_type, fun j ↦ j.elim0⟩

/-- A progression with no nonzero relation in the `2`-dilate of its coefficient box is `2`-proper.
Indeed a relation `v` in the coefficient box of `P + P` has `|v i| ≤ 2 * (P.length i - 1)`. -/
lemma proper_add_self_of_shortRelationRank_eq_zero {P : GAP G}
    (hrank : P.shortRelationRank 2 = 0) : (P + P).Proper := by
  rw [proper_add_self_iff]
  intro v hv hlt
  by_contra hne
  obtain ⟨i₀, -⟩ := Function.ne_iff.1 hne
  have hshort : IsShort P.halfWidth 2 v := by
    intro i
    rw [← Int.cast_abs, P.cast_halfWidth]
    exact_mod_cast (by grind [P.length_pos i, hlt i] : |v i| ≤ 2 * ((P.length i : ℤ) - 1))
  grind [le_shortRelationRank (Nat.succ_le_of_lt i₀.pos)
    ⟨fun _ ↦ v, linearIndependent_unique_iff.mpr hne, fun _ ↦ ⟨hv, hshort⟩⟩]

/-! ### The short relations and their saturated span -/

/-- A family of `P.shortRelationRank t` linearly independent relations of `P` in the `t`-dilate of
its coefficient box. -/
def shortRelations (P : GAP G) (t : ℝ) : Fin (P.shortRelationRank t) → Fin P.dim → ℤ :=
  (P.hasIndependentShort_shortRelationRank t).choose

lemma linearIndependent_shortRelations (P : GAP G) (t : ℝ) :
    LinearIndependent ℤ (P.shortRelations t) := by
  obtain ⟨h, -⟩ := (P.hasIndependentShort_shortRelationRank t).choose_spec
  exact h

lemma shortRelations_mem_relations (P : GAP G) (t : ℝ) (j : Fin (P.shortRelationRank t)) :
    P.shortRelations t j ∈ P.relations := by
  obtain ⟨-, h⟩ := (P.hasIndependentShort_shortRelationRank t).choose_spec
  obtain ⟨hj, -⟩ := h j
  exact hj

lemma isShort_shortRelations (P : GAP G) (t : ℝ) (j : Fin (P.shortRelationRank t)) :
    IsShort P.halfWidth t (P.shortRelations t j) := by
  obtain ⟨-, h⟩ := (P.hasIndependentShort_shortRelationRank t).choose_spec
  obtain ⟨-, hj⟩ := h j
  exact hj

lemma span_shortRelations_le_relations (P : GAP G) (t : ℝ) :
    Submodule.span ℤ (Set.range (P.shortRelations t)) ≤ AddSubgroup.toIntSubmodule P.relations := by
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact P.shortRelations_mem_relations t j

/-- The saturated span of the short relations: the integer vectors in their real span. -/
abbrev shortRelationSpan (P : GAP G) (t : ℝ) : Submodule ℤ (Fin P.dim → ℤ) :=
  saturatedSpan (Finset.univ.image (P.shortRelations t))

lemma finrank_shortRelationSpan (P : GAP G) (t : ℝ) :
    Module.finrank ℤ (P.shortRelationSpan t) = P.shortRelationRank t := by
  rw [shortRelationSpan, finrank_saturatedSpan,
    finrank_integerGeneratedSubspace_image (P.linearIndependent_shortRelations t)]

/-- The saturated span of the short relations has a Smith normal form of rank
`P.shortRelationRank t`. -/
lemma nonempty_smithNormalForm_shortRelationSpan (P : GAP G) (t : ℝ) :
    Nonempty (Module.Basis.SmithNormalForm (P.shortRelationSpan t) (Fin P.dim)
      (P.shortRelationRank t)) := by
  obtain ⟨n, snf⟩ := (P.shortRelationSpan t).smithNormalForm (Pi.basisFun ℤ (Fin P.dim))
  obtain rfl : n = P.shortRelationRank t := by
    rw [← P.finrank_shortRelationSpan t, Module.finrank_eq_card_basis snf.bN, Fintype.card_fin]
  exact ⟨snf⟩

/-- Every relation in the `t`-dilate of the coefficient box lies in the saturated span of the short
relations. Otherwise adding it to the short relations would give `P.shortRelationRank t + 1`
independent relations in the dilate. -/
lemma mem_shortRelationSpan {P : GAP G} {t : ℝ} {w : Fin P.dim → ℤ} (hw : w ∈ P.relations)
    (hshort : IsShort P.halfWidth t w) : w ∈ P.shortRelationSpan t := by
  by_contra hspan
  have hindep : LinearIndependent ℤ (Fin.cons w (P.shortRelations t)) := by
    refine .finCons' w _ (P.linearIndependent_shortRelations t) ?_
    intro c y hy hcy
    by_contra hc
    have hcw : c • w ∈ P.shortRelationSpan t := by
      rw [eq_neg_of_add_eq_zero_left hcy]
      exact neg_mem (span_range_le_saturatedSpan _ hy)
    exact hspan (mem_saturatedSpan_of_zsmul_mem hc hcw)
  grind [le_shortRelationRank (by simpa using hindep.fintype_card_le_finrank)
    ⟨_, hindep, Fin.cases ⟨hw, hshort⟩ fun j ↦
      ⟨P.shortRelations_mem_relations t j, P.isShort_shortRelations t j⟩⟩]

/-- The image under the step map of a vector in the saturated span of the short relations lies in
the image of the `2 * d`-dilate of the coefficient box. Indeed rounding the coefficients of its
expansion in the short relations leaves a vector of that dilate with the same image. -/
lemma stepHom_mem_boundedStepImage_of_mem_shortRelationSpan [DecidableEq G] {P : GAP G}
    {x : Fin P.dim → ℤ} (hx : x ∈ P.shortRelationSpan 2) :
    stepHom P x ∈ P.boundedStepImage (2 * P.dim) := by
  obtain ⟨y, hxy, hy⟩ := exists_congr_span_isShort (P.isShort_shortRelations 2) hx
  have hstep : stepHom P x = stepHom P y := by
    rw [← sub_eq_zero, ← map_sub]
    exact P.span_shortRelations_le_relations 2 hxy
  rw [hstep]
  refine stepHom_mem_boundedStepImage (mem_intBox_of_abs_le ?_)
  intro i
  refine (hy i).trans ?_
  push_cast
  nlinarith [(Nat.cast_le.mpr (P.shortRelationRank_le_dim 2) : (_ : ℝ) ≤ P.dim),
    (Nat.cast_nonneg (P.halfWidth i) : (0 : ℝ) ≤ _)]

/-- Multiples of a nonzero element of a prime cyclic group are distinct below the modulus. -/
lemma injOn_nsmul_of_prime {q : ℕ} (hq : Nat.Prime q) {a : ZMod q} (ha : a ≠ 0) :
    Set.InjOn (fun n : ℕ ↦ n • a) (Set.Iio q) := by
  have : Fact q.Prime := ⟨hq⟩
  intro m hm n hn h
  simp only [nsmul_eq_mul] at h
  rw [← ZMod.val_cast_of_lt hm, ← ZMod.val_cast_of_lt hn, mul_right_cancel₀ ha h]

/-- Multiples of a nonzero element of a torsion-free group are distinct. -/
lemma injOn_nsmul_of_isAddTorsionFree [IsAddTorsionFree G] (N : ℕ) {a : G} (ha : a ≠ 0) :
    Set.InjOn (fun n : ℕ ↦ n • a) (Set.Iio N) :=
  ((IsAddLeftRegular.all a).nsmul_injective ha).injOn

/-- Suppose that the multiples `n • a` with `n < N` of every nonzero `a` are distinct, as in a
cyclic group of prime order `N` or in a torsion-free group, and that
`(2 * (2 * d) + 1) ^ d * #P.carrier < N`. Then the saturated span of the short relations of `P`
consists of relations. Otherwise the first `N` multiples of the image of a vector in the span that
is not a relation would be `N` distinct elements of the image of the `2 * d`-dilate of the
coefficient box. -/
lemma shortRelationSpan_le_relations [DecidableEq G] {N : ℕ} {P : GAP G}
    (hG : ∀ a : G, a ≠ 0 → Set.InjOn (fun n : ℕ ↦ n • a) (Set.Iio N))
    (hcard : (2 * (2 * P.dim) + 1) ^ P.dim * P.carrier.card < N) :
    (P.shortRelationSpan 2).toAddSubgroup ≤ P.relations := by
  intro x hx
  by_contra hrel
  have hmaps : Set.MapsTo (fun n : ℕ ↦ n • stepHom P x) (Finset.range N)
      (P.boundedStepImage (2 * P.dim)) := by
    intro n _
    dsimp only
    rw [← map_nsmul]
    exact stepHom_mem_boundedStepImage_of_mem_shortRelationSpan (nsmul_mem hx n)
  grind [Finset.card_le_card_of_injOn _ hmaps (by simpa using hG (stepHom P x) hrel),
    Finset.card_range, P.card_boundedStepImage_le (2 * P.dim)]

/-! ### Projecting by a saturated span -/

/-- The image of the coefficient box after quotienting by a saturated span in Smith
coordinates. -/
def smithQuotientBody (P : GAP G) {n : ℕ} {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    Set (Fin (P.dim - n) → ℝ) :=
  smithRealQuotientMap snf '' BoxLattice.realBox P.halfWidth

lemma isCompact_smithQuotientBody {P : GAP G} {n : ℕ} {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    IsCompact (P.smithQuotientBody snf) :=
  (BoxLattice.isCompact_realBox P.halfWidth).image
    (LinearMap.continuous_of_finiteDimensional (smithRealQuotientMap snf))

/-- The integer points of the projected coefficient box. -/
def smithQuotientIntegerPoints (P : GAP G) {n : ℕ} {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    Set (Fin (P.dim - n) → ℤ) :=
  {v | intVectorToReal v ∈ P.smithQuotientBody snf}

lemma smithQuotientIntegerPoints_finite {P : GAP G} {n : ℕ} {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    (P.smithQuotientIntegerPoints snf).Finite := by
  let L : AddSubgroup (Fin (P.dim - n) → ℝ) := (⊤ : AddSubgroup _).map intVectorToReal
  have : DiscreteTopology L := BoxLattice.discreteTopology_map ⊤
  have hinter : (P.smithQuotientBody snf ∩ (L : Set (Fin (P.dim - n) → ℝ))).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      (P.isCompact_smithQuotientBody snf).isBounded AddSubgroup.isClosed_of_discreteTopology
  refine Set.Finite.of_finite_image (hinter.subset ?_) intVectorToReal_injective.injOn
  rintro x ⟨v, hv, rfl⟩
  exact ⟨hv, AddSubgroup.mem_map.mpr ⟨v, Set.mem_univ v, rfl⟩⟩

/-- The finite set of integer points of the projected coefficient box. -/
def smithQuotientCoords (P : GAP G) {n : ℕ} {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    Finset (Fin (P.dim - n) → ℤ) :=
  (smithQuotientIntegerPoints_finite snf).toFinset

lemma mem_smithQuotientCoords {P : GAP G} {n : ℕ} {S : Finset (Fin P.dim → ℤ)}
    {snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n}
    {v : Fin (P.dim - n) → ℤ} :
    v ∈ P.smithQuotientCoords snf ↔ intVectorToReal v ∈ P.smithQuotientBody snf := by
  rw [smithQuotientCoords, Set.Finite.mem_toFinset]
  rfl

/-- The integer points of the projected coefficient box lie in a proper GAP of dimension at most
`d - n` whose size exceeds their number by a factor depending only on `d - n`. -/
lemma exists_proper_gap_smithQuotientCoords {P : GAP G} {n : ℕ} {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n) :
    ∃ Q : GAP (Fin (P.dim - n) → ℤ), Q.Proper ∧
      P.smithQuotientCoords snf ⊆ Q.carrier ∧ Q.dim ≤ P.dim - n ∧
      Q.carrier.card ≤ latticeBoxFactor (P.dim - n) * (P.smithQuotientCoords snf).card :=
  exists_proper_gap_image_realBox P.halfWidth_pos (smithRealQuotientMap_intCast snf)
    (smithRealQuotientMap_surjective snf) fun _ ↦ mem_smithQuotientCoords

/-- The coefficient vectors of the points of `P` map to integer points of the projected
coefficient box. -/
lemma smithQuotientMap_mem_smithQuotientCoords {P : GAP G} {n : ℕ} {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n)
    {v : Fin P.dim → ℤ} (hv : v ∈ symBox P) :
    smithQuotientMap snf v ∈ P.smithQuotientCoords snf := by
  rw [mem_smithQuotientCoords, ← smithRealQuotientMap_intCast]
  refine ⟨intVectorToReal v, ?_, rfl⟩
  rw [BoxLattice.mem_realBox]
  intro i
  rw [intVectorToReal_apply, ← Int.cast_abs, P.cast_halfWidth]
  exact_mod_cast (by grind [mem_symBox.mp hv i] : |v i| ≤ (P.length i : ℤ) - 1)

/-- If a saturated span consists of relations, then `P` lies in the image of every progression
containing the integer points of the projected coefficient box, translated by the origin of `P`. -/
lemma carrier_subset_shift_map [DecidableEq G] {P : GAP G} {n : ℕ} {S : Finset (Fin P.dim → ℤ)}
    {snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n}
    (hrel : (saturatedSpan S).toAddSubgroup ≤ P.relations)
    {Q : GAP (Fin (P.dim - n) → ℤ)} (hQ : P.smithQuotientCoords snf ⊆ Q.carrier) :
    P.carrier ⊆ ((Q.map (stepsHom (P.smithQuotientStep snf))).shift P.origin).carrier := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := P.mem_carrier_iff_exists_intCoeffs.mp hx
  have hcQ : smithQuotientMap snf c ∈ Q.carrier := by
    refine hQ (smithQuotientMap_mem_smithQuotientCoords snf (mem_symBox.mpr ?_))
    intro i
    grind [abs_of_nonneg, hc i]
  rw [carrier_shift, carrier_map]
  refine Finset.mem_image.mpr ⟨_, Finset.mem_image_of_mem _ hcQ, ?_⟩
  rw [P.stepHom_smithQuotientMap snf hrel]
  exact add_comm _ _

/-- If a saturated span of rank `n` consists of relations, then `P` lies in a GAP of dimension at
most `d - n` whose size exceeds the number of integer points of the projected coefficient box by
a factor depending only on `d - n`. -/
lemma exists_carrier_subset_dim_le_card_le_of_saturatedSpan_le_relations [DecidableEq G]
    {P : GAP G} {n : ℕ} {S : Finset (Fin P.dim → ℤ)}
    (snf : Module.Basis.SmithNormalForm (saturatedSpan S) (Fin P.dim) n)
    (hrel : (saturatedSpan S).toAddSubgroup ≤ P.relations) :
    ∃ Q : GAP G, P.carrier ⊆ Q.carrier ∧ Q.dim ≤ P.dim - n ∧
      (Q.carrier.card : ℝ) ≤
        latticeBoxFactor (P.dim - n) * (P.smithQuotientCoords snf).card := by
  obtain ⟨Q, -, hQ, hdim, hcard⟩ := exists_proper_gap_smithQuotientCoords snf
  refine ⟨_, carrier_subset_shift_map hrel hQ, (Q.dim_map_le _).trans hdim, ?_⟩
  rw [carrier_shift]
  exact_mod_cast (Finset.card_image_le.trans (Q.card_map_le _)).trans hcard

/-! ### Counting the projected integer points

From here on the saturated span is that of the short relations, and `r` denotes the short rank
`P.shortRelationRank 2`. -/

/-- Let `y` be an integer point of the quotient that is the image of a real vector `b`. Then `y` is
the image of an integer vector `z` with `|z i| ≤ |b i| + r * (2 * P.halfWidth i)`. Indeed the lift
of `y` with zero coordinates along the span differs from `b` by a real combination of the short
relations, whose coefficients can be rounded. -/
lemma exists_smithQuotientMap_eq_of_smithRealQuotientMap_eq {P : GAP G} {n : ℕ}
    (snf : Module.Basis.SmithNormalForm (P.shortRelationSpan 2) (Fin P.dim) n)
    {y : Fin (P.dim - n) → ℤ} {b : Fin P.dim → ℝ}
    (hb : smithRealQuotientMap snf b = intVectorToReal y) :
    ∃ z, smithQuotientMap snf z = y ∧
      ∀ i, |(z i : ℝ)| ≤ |b i| + P.shortRelationRank 2 * (2 * P.halfWidth i) := by
  have hspan : intVectorToReal (smithQuotientLift snf y) - b ∈
      integerGeneratedSubspace (Finset.univ.image (P.shortRelations 2)) := by
    rw [← smithRealQuotientMap_eq_zero_iff snf, map_sub, smithRealQuotientMap_intCast,
      smithQuotientMap_lift, hb, sub_self]
  rw [integerGeneratedSubspace_image_univ] at hspan
  obtain ⟨z, hz, hbound⟩ := exists_congr_close_isShort (P.isShort_shortRelations 2) hspan
  refine ⟨z, ?_, hbound⟩
  rw [← smithQuotientMap_lift snf y, eq_comm, smithQuotientMap_eq_iff]
  exact span_range_le_saturatedSpan _ hz

/-- Every integer point of the projected coefficient box is the image of an integer vector in the
`(2 * r + 1)`-dilate of the coefficient box. -/
lemma exists_bounded_lift_smithQuotientCoords {P : GAP G} {n : ℕ}
    {snf : Module.Basis.SmithNormalForm (P.shortRelationSpan 2) (Fin P.dim) n}
    {y : Fin (P.dim - n) → ℤ} (hy : y ∈ P.smithQuotientCoords snf) :
    ∃ z ∈ intBox fun i ↦ (2 * P.shortRelationRank 2 + 1) * P.halfWidth i,
      smithQuotientMap snf z = y := by
  obtain ⟨b, hb, hby⟩ := mem_smithQuotientCoords.mp hy
  obtain ⟨z, hzy, hz⟩ := exists_smithQuotientMap_eq_of_smithRealQuotientMap_eq snf hby
  refine ⟨z, mem_intBox_of_abs_le ?_, hzy⟩
  intro i
  push_cast
  linarith [hz i, BoxLattice.mem_realBox.mp hb i]

/-- If the saturated span of the short relations consists of relations, then the image in the group
of the integer points of the projected coefficient box lies in the image of the `(2 * r + 1)`-dilate
of the coefficient box, so it has at most `(2 * (2 * r + 1) + 1) ^ d * #P.carrier` elements. -/
lemma card_image_smithQuotientCoords_le [DecidableEq G] {P : GAP G} {n : ℕ}
    (snf : Module.Basis.SmithNormalForm (P.shortRelationSpan 2) (Fin P.dim) n)
    (hrel : (P.shortRelationSpan 2).toAddSubgroup ≤ P.relations) :
    ((P.smithQuotientCoords snf).image (stepsHom (P.smithQuotientStep snf))).card ≤
      (2 * (2 * P.shortRelationRank 2 + 1) + 1) ^ P.dim * P.carrier.card := by
  refine (Finset.card_le_card ?_).trans (P.card_boundedStepImage_le _)
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨z, hz, rfl⟩ := exists_bounded_lift_smithQuotientCoords hy
  rw [P.stepHom_smithQuotientMap snf hrel]
  exact stepHom_mem_boundedStepImage hz

/-- Two integer points of the projected coefficient box with the same image in the group differ by
the image of a relation in the `(2 * r + 2)`-dilate of the coefficient box. -/
lemma exists_bounded_relation_of_stepsHom_eq {P : GAP G} {n : ℕ}
    {snf : Module.Basis.SmithNormalForm (P.shortRelationSpan 2) (Fin P.dim) n}
    (hrel : (P.shortRelationSpan 2).toAddSubgroup ≤ P.relations)
    {y y₀ : Fin (P.dim - n) → ℤ} (hy : y ∈ P.smithQuotientCoords snf)
    (hy₀ : y₀ ∈ P.smithQuotientCoords snf)
    (himage : stepsHom (P.smithQuotientStep snf) y = stepsHom (P.smithQuotientStep snf) y₀) :
    ∃ z ∈ P.relations, smithQuotientMap snf z = y - y₀ ∧
      z ∈ intBox fun i ↦ (2 * P.shortRelationRank 2 + 2) * P.halfWidth i := by
  obtain ⟨b, hb, hby⟩ := mem_smithQuotientCoords.mp hy
  obtain ⟨b₀, hb₀, hby₀⟩ := mem_smithQuotientCoords.mp hy₀
  obtain ⟨z, hzy, hz⟩ := exists_smithQuotientMap_eq_of_smithRealQuotientMap_eq snf
    (y := y - y₀) (b := b - b₀) (by simp [hby, hby₀])
  refine ⟨z, AddMonoidHom.mem_ker.mpr ?_, hzy, mem_intBox_of_abs_le ?_⟩
  · rw [← P.stepHom_smithQuotientMap snf hrel, hzy, map_sub, himage, sub_self]
  · intro i
    simp only [Pi.sub_apply] at hz
    push_cast
    linarith [hz i, abs_sub (b i) (b₀ i), BoxLattice.mem_realBox.mp hb i,
      BoxLattice.mem_realBox.mp hb₀ i]

/-- Two relations of `P` with distinct images in the quotient are separated by the `2`-dilate of
the coefficient box. Otherwise their difference would be a relation in the `2`-dilate outside the
saturated span of the short relations. -/
lemma exists_lt_abs_sub_of_smithQuotientMap_ne {P : GAP G} {n : ℕ}
    {snf : Module.Basis.SmithNormalForm (P.shortRelationSpan 2) (Fin P.dim) n}
    {z z' : Fin P.dim → ℤ} (hz : z ∈ P.relations) (hz' : z' ∈ P.relations)
    (hne : smithQuotientMap snf z ≠ smithQuotientMap snf z') :
    ∃ i, ((2 * P.halfWidth i : ℕ) : ℤ) < |z i - z' i| := by
  by_contra! h
  refine hne ((smithQuotientMap_eq_iff snf z z').mpr (mem_shortRelationSpan
    (P.relations.sub_mem hz hz') ?_))
  intro i
  exact_mod_cast h i

/-- Relations of `P` in the `(2 * r + 2)`-dilate of the coefficient box with distinct images in the
quotient number at most `(2 * r + 4) ^ d`, by the packing bound. -/
lemma card_le_of_injOn_smithQuotientMap {P : GAP G} {n : ℕ}
    {snf : Module.Basis.SmithNormalForm (P.shortRelationSpan 2) (Fin P.dim) n}
    {Z : Finset (Fin P.dim → ℤ)} (hrel : ∀ z ∈ Z, z ∈ P.relations)
    (hbox : Z ⊆ intBox fun i ↦ (2 * P.shortRelationRank 2 + 2) * P.halfWidth i)
    (hinj : Set.InjOn (smithQuotientMap snf) Z) :
    Z.card ≤ (2 * P.shortRelationRank 2 + 4) ^ P.dim := by
  refine Nat.le_of_mul_le_mul_right ((card_mul_prod_le_of_separated hbox
    fun u hu w hw huw ↦ exists_lt_abs_sub_of_smithQuotientMap_ne (hrel u hu) (hrel w hw)
      (hinj.ne hu hw huw)).trans ?_) (by positivity)
  rw [← Fin.prod_const, ← Finset.prod_mul_distrib]
  gcongr
  nlinarith

variable [DecidableEq G]

/-- If the saturated span of the short relations consists of relations, then each fiber of the
map to the group on the integer points of the projected coefficient box has at most
`(2 * r + 4) ^ d` elements. -/
lemma card_filter_stepsHom_eq_le {P : GAP G} {n : ℕ}
    {snf : Module.Basis.SmithNormalForm (P.shortRelationSpan 2) (Fin P.dim) n}
    (hrel : (P.shortRelationSpan 2).toAddSubgroup ≤ P.relations)
    {y₀ : Fin (P.dim - n) → ℤ} (hy₀ : y₀ ∈ P.smithQuotientCoords snf) :
    ((P.smithQuotientCoords snf).filter fun y ↦
      stepsHom (P.smithQuotientStep snf) y = stepsHom (P.smithQuotientStep snf) y₀).card ≤
        (2 * P.shortRelationRank 2 + 4) ^ P.dim := by
  set F := (P.smithQuotientCoords snf).filter fun y ↦
    stepsHom (P.smithQuotientStep snf) y = stepsHom (P.smithQuotientStep snf) y₀
  have hlift : ∀ y ∈ F, ∃ z ∈ P.relations, smithQuotientMap snf z = y - y₀ ∧
      z ∈ intBox fun i ↦ (2 * P.shortRelationRank 2 + 2) * P.halfWidth i := by
    intro y hy
    obtain ⟨hy, himage⟩ := Finset.mem_filter.mp hy
    exact exists_bounded_relation_of_stepsHom_eq hrel hy hy₀ himage
  choose! z hzrel hzmap hzbox using hlift
  have hinj : Set.InjOn (smithQuotientMap snf ∘ z) F := by
    intro a ha b hb hab
    simpa [hzmap a ha, hzmap b hb] using hab
  rw [← Finset.card_image_of_injOn hinj.of_comp]
  apply card_le_of_injOn_smithQuotientMap
  · simpa using hzrel
  · simpa [Finset.image_subset_iff] using hzbox
  · rw [Finset.coe_image]
    exact hinj.image_of_comp

/-- If the saturated span of the short relations consists of relations, then the projected
coefficient box has at most `((2 * r + 4) * (2 * (2 * r + 1) + 1)) ^ d * #P.carrier` integer
points, by the bound on their image in the group and the bound on each fiber. -/
lemma card_smithQuotientCoords_le {P : GAP G} {n : ℕ}
    (snf : Module.Basis.SmithNormalForm (P.shortRelationSpan 2) (Fin P.dim) n)
    (hrel : (P.shortRelationSpan 2).toAddSubgroup ≤ P.relations) :
    (P.smithQuotientCoords snf).card ≤
      ((2 * P.shortRelationRank 2 + 4) * (2 * (2 * P.shortRelationRank 2 + 1) + 1)) ^ P.dim *
        P.carrier.card := by
  refine (Finset.card_le_mul_card_image (f := stepsHom (P.smithQuotientStep snf)) _
    ((2 * P.shortRelationRank 2 + 4) ^ P.dim) ?_).trans ?_
  · intro g hg
    obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.mp hg
    exact card_filter_stepsHom_eq_le hrel hy₀
  · rw [mul_pow, mul_assoc]
    exact Nat.mul_le_mul_left _ (card_image_smithQuotientCoords_le snf hrel)

/-! ### One step of properization -/

/-- One step of properization. Suppose that the multiples `n • a` with `n < N` of every nonzero `a`
are distinct and that `(2 * (2 * d) + 1) ^ d * #P.carrier < N`. Then either `P` is `2`-proper, or
dividing by the saturated span of the short relations gives a GAP of smaller dimension containing
`P`, of size at most `exp (2 * (d + 2) ^ 2 * log (d + 2)) * #P.carrier`. -/
lemma proper_add_self_or_exists_gap_dim_lt {N : ℕ} {P : GAP G}
    (hG : ∀ a : G, a ≠ 0 → Set.InjOn (fun n : ℕ ↦ n • a) (Set.Iio N))
    (hcard : (2 * (2 * P.dim) + 1) ^ P.dim * P.carrier.card < N) :
    (P + P).Proper ∨ ∃ Q : GAP G, P.carrier ⊆ Q.carrier ∧ Q.dim < P.dim ∧
      Q.carrier.card ≤ Real.exp (2 * (P.dim + 2) ^ 2 * Real.log (P.dim + 2)) * P.carrier.card := by
  by_cases hrank : P.shortRelationRank 2 = 0
  · exact Or.inl (proper_add_self_of_shortRelationRank_eq_zero hrank)
  obtain ⟨snf⟩ := P.nonempty_smithNormalForm_shortRelationSpan 2
  have hrel := shortRelationSpan_le_relations hG hcard
  obtain ⟨Q, hPQ, hdim, hQcard⟩ :=
    exists_carrier_subset_dim_le_card_le_of_saturatedSpan_le_relations snf hrel
  have hcoords : ((P.smithQuotientCoords snf).card : ℝ) ≤
      ((2 * (P.shortRelationRank 2 : ℝ) + 4) * (2 * (2 * (P.shortRelationRank 2 : ℝ) + 1) + 1)) ^
        P.dim * P.carrier.card := by
    exact_mod_cast card_smithQuotientCoords_le snf hrel
  refine Or.inr ⟨Q, hPQ, hdim.trans_lt (by grind [P.shortRelationRank_le_dim 2]),
    hQcard.trans ((mul_le_mul_of_nonneg_left hcoords (by positivity)).trans ?_)⟩
  rw [← mul_assoc]
  gcongr
  exact latticeBoxFactor_mul_pow_le_exp (P.shortRelationRank_le_dim 2)

end GAP

/-! ## Iterated properization -/

/-- The exponent `2 * (d + 2) ^ 3 * log (d + 2)` in the size bound of properization. -/
def properizationExponent (d : ℝ) : ℝ := 2 * (d + 2) ^ 3 * Real.log (d + 2)

lemma properizationExponent_nonneg {d : ℝ} (hd : 0 ≤ d) : 0 ≤ properizationExponent d :=
  mul_nonneg (mul_nonneg zero_le_two (pow_nonneg (by linarith) 3)) (log_add_two_pos hd).le

lemma properizationExponent_mono {d d' : ℝ} (hd : 0 ≤ d) (hdd' : d ≤ d') :
    properizationExponent d ≤ properizationExponent d' := by
  rw [properizationExponent, properizationExponent, mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (add_two_pow_three_mul_log_le hd hdd') zero_le_two

/-- For `0 ≤ x`, `2 * (x + 2) ^ 2 * log (x + 2)`, the exponent of one step of properization, is at
most `properizationExponent x`. -/
lemma mul_sq_mul_log_le_properizationExponent {x : ℝ} (hx : 0 ≤ x) :
    2 * (x + 2) ^ 2 * Real.log (x + 2) ≤ properizationExponent x := by
  rw [properizationExponent]
  nlinarith [two_mul_add_two_sq_mul_log_le hx,
    mul_nonneg (pow_nonneg (by linarith : 0 ≤ x + 2) 3) (log_add_two_pos hx).le]

/-- If `exp (properizationExponent d) * #P.carrier ≤ N`, then `P` satisfies the hypothesis
`(2 * (2 * d) + 1) ^ d * #P.carrier < N` of `GAP.proper_add_self_or_exists_gap_dim_lt`. -/
lemma GAP.mul_card_lt_of_exp_mul_card_le [DecidableEq G] {N : ℕ} {P : GAP G}
    (hcard : Real.exp (properizationExponent P.dim) * P.carrier.card ≤ N) :
    (2 * (2 * P.dim) + 1) ^ P.dim * P.carrier.card < N := by
  have hexp : Real.exp (((P.dim : ℝ) + 2) ^ 2 * Real.log ((P.dim : ℝ) + 2)) <
      Real.exp (properizationExponent P.dim) := by
    rw [Real.exp_lt_exp]
    linarith [mul_sq_mul_log_le_properizationExponent (Nat.cast_nonneg (α := ℝ) P.dim),
      mul_pos (pow_pos (by positivity : (0 : ℝ) < (P.dim : ℝ) + 2) 2)
        (log_add_two_pos (Nat.cast_nonneg (α := ℝ) P.dim))]
  exact_mod_cast ((mul_le_mul_of_nonneg_right (two_mul_two_mul_add_one_pow_le_exp P.dim)
    (Nat.cast_nonneg _)).trans_lt (mul_lt_mul_of_pos_right hexp
      (mod_cast P.nonempty.card_pos))).trans_le hcard

/-- For `e < d` and `0 ≤ x`, writing `E` for `properizationExponent`,
`exp (E e) * (exp (2 * (d + 2) ^ 2 * log (d + 2)) * x) ≤ exp (E d) * x`. -/
lemma exp_mul_exp_mul_le_of_lt {e d : ℕ} (hed : e < d) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (properizationExponent e) *
        (Real.exp (2 * ((d : ℝ) + 2) ^ 2 * Real.log ((d : ℝ) + 2)) * x) ≤
      Real.exp (properizationExponent d) * x := by
  rw [← mul_assoc, ← Real.exp_add]
  gcongr
  exact mul_pow_three_mul_log_add_le zero_le_two hed

variable [DecidableEq G]

/-- Let `P` be a GAP of dimension `d` in an abelian group in which the multiples `n • a` with
`n < N` of every nonzero `a` are distinct. Write `E d = 2 * (d + 2) ^ 3 * log (d + 2)` for
`properizationExponent d` and suppose `exp (E d) * #P.carrier ≤ N`. Then `P` lies in a `2`-proper
GAP of dimension at most `d` and of size at most `exp (E d) * #P.carrier`. The proof iterates
`GAP.proper_add_self_or_exists_gap_dim_lt`: each step costs a factor
`exp (2 * (d + 2) ^ 2 * log (d + 2))` and either finds that the progression is `2`-proper or
lowers the dimension. -/
lemma exists_twoProperGAP_carrier_subset_dim_le_card_le_of_injOn_nsmul {N : ℕ} (P : GAP G)
    (hG : ∀ a : G, a ≠ 0 → Set.InjOn (fun n : ℕ ↦ n • a) (Set.Iio N))
    (hcard : Real.exp (properizationExponent P.dim) * P.carrier.card ≤ N) :
    ∃ Q : GAP G, (Q + Q).Proper ∧ P.carrier ⊆ Q.carrier ∧ Q.dim ≤ P.dim ∧
      Q.carrier.card ≤ Real.exp (properizationExponent P.dim) * P.carrier.card := by
  induction hd : P.dim using Nat.strong_induction_on generalizing P with
  | h d ih =>
    subst hd
    rcases GAP.proper_add_self_or_exists_gap_dim_lt hG
      (GAP.mul_card_lt_of_exp_mul_card_le hcard) with hP | ⟨Q, hPQ, hdim, hQcard⟩
    · refine ⟨P, hP, subset_rfl, le_rfl, le_mul_of_one_le_left (Nat.cast_nonneg _) ?_⟩
      exact Real.one_le_exp (properizationExponent_nonneg (Nat.cast_nonneg _))
    · have hQbound := mul_le_mul_of_nonneg_left hQcard
        (Real.exp_pos (properizationExponent Q.dim)).le
      obtain ⟨R, hR, hQR, hRdim, hRcard⟩ := ih Q.dim hdim Q
        (hQbound.trans ((exp_mul_exp_mul_le_of_lt hdim (by positivity)).trans hcard)) rfl
      exact ⟨R, hR, hPQ.trans hQR, hRdim.trans hdim.le,
        hRcard.trans (hQbound.trans (exp_mul_exp_mul_le_of_lt hdim (by positivity)))⟩

/-- Properization in `ZMod q` for a prime `q` with
`exp (properizationExponent d) * #P.carrier ≤ q`. -/
lemma exists_twoProperGAP_zmod_carrier_subset_dim_le_card_le {q : ℕ} (P : GAP (ZMod q))
    (hq : Nat.Prime q) (hcard : Real.exp (properizationExponent P.dim) * P.carrier.card ≤ q) :
    ∃ Q : GAP (ZMod q), (Q + Q).Proper ∧ P.carrier ⊆ Q.carrier ∧ Q.dim ≤ P.dim ∧
      Q.carrier.card ≤ Real.exp (properizationExponent P.dim) * P.carrier.card :=
  exists_twoProperGAP_carrier_subset_dim_le_card_le_of_injOn_nsmul P
    (fun _ ha ↦ GAP.injOn_nsmul_of_prime hq ha) hcard

/-- Properization in a torsion-free group, such as `ℤ`, with no condition on `#P.carrier`. -/
lemma exists_twoProperGAP_carrier_subset_dim_le_card_le_of_isAddTorsionFree [IsAddTorsionFree G]
    (P : GAP G) :
    ∃ Q : GAP G, (Q + Q).Proper ∧ P.carrier ⊆ Q.carrier ∧ Q.dim ≤ P.dim ∧
      Q.carrier.card ≤ Real.exp (properizationExponent P.dim) * P.carrier.card :=
  exists_twoProperGAP_carrier_subset_dim_le_card_le_of_injOn_nsmul P
    (fun _ ha ↦ GAP.injOn_nsmul_of_isAddTorsionFree _ ha) (Nat.le_ceil _)

end

end ChangFreimanRuzsa
