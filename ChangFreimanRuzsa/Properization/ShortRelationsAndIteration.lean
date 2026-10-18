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

This submodule develops the successive-minimum argument, saturated quotient reduction, and the
iteration producing a two-proper generalized arithmetic progression.
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
  have := hlen i
  rw [halfWidth]
  omega

lemma cast_halfWidth (P : GAP G) (i : Fin P.dim) :
    ((P.halfWidth i : ℕ) : ℝ) = (P.length i : ℝ) - 1 := by
  rw [halfWidth, Nat.cast_sub (P.length_pos i), Nat.cast_one]

/-! ### The rank of the short relations

The relation lattice of a progression in `ZMod q` has full rank, since it contains `q ℤ ^ dim`,
but that of a progression in `ℤ` does not. The rank reduction therefore does not use the
successive minima of the relation lattice. It uses the largest number of linearly independent
relations in a fixed dilate of the coefficient box, which is defined in every group. -/

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

/-- Smith normal form for the saturated span of a maximal independent family below the cutoff.
The eliminated Smith rank is exactly `shortRelationRank`. -/
theorem exists_smithNormalForm_shortRelations (P : GAP G) (t : ℝ) :
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
  have hn : n = P.shortRelationRank t := by
    rw [Module.finrank_eq_card_basis snf.bN, Fintype.card_fin] at hrank
    exact hrank
  subst n
  exact ⟨v, S, snf, hS, hindep, fun j ↦ (hv j).1, fun j ↦ (hv j).2⟩

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
  have hvR : LinearIndependent ℝ (fun j ↦ intVectorToReal (v j)) := by
    change LinearIndependent ℝ (fun j i ↦ (v j i : ℝ))
    have h := (linearIndependent_algebraMap_comp_iff
      (R := ℤ) (S := ℝ) (ι' := Fin P.dim)).mpr hindep
    change LinearIndependent ℝ (fun j i ↦ algebraMap ℤ ℝ (v j i)) at h
    exact h
  have hwR : intVectorToReal w ∉
      Submodule.span ℝ (Set.range fun j ↦ intVectorToReal (v j)) := by
    intro hw
    apply hwspan
    change intVectorToReal w ∈ integerGeneratedSubspace (Finset.univ.image v)
    change intVectorToReal w ∈
      Submodule.span ℝ
        (intVectorToReal '' (↑(Finset.univ.image v) : Set (Fin P.dim → ℤ)))
    have hset :
        intVectorToReal '' (↑(Finset.univ.image v) : Set (Fin P.dim → ℤ)) =
          Set.range fun j ↦ intVectorToReal (v j) := by
      ext z
      constructor
      · rintro ⟨u, hu, rfl⟩
        rw [Finset.mem_coe, Finset.mem_image] at hu
        obtain ⟨j, -, rfl⟩ := hu
        exact ⟨j, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨v j, by simp, rfl⟩
    rwa [hset]
  have hconsR : LinearIndependent ℝ
      (Fin.cons (intVectorToReal w) fun j ↦ intVectorToReal (v j)) :=
    linearIndependent_finCons.mpr ⟨hvR, hwR⟩
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
      · funext k
        rfl
      · intro j
        funext k
        rfl
    rw [heq]
    exact hconsR
  have hrd : r < P.dim := by
    have hcard := hcons.fintype_card_le_finrank
    rw [Module.finrank_fin_fun] at hcard
    simp only [Fintype.card_fin] at hcard
    omega
  have hfamily : HasIndependentShort P.relations P.halfWidth (r + 1) 3 := by
    refine ⟨Fin.cons w v, hcons, ?_⟩
    apply Fin.cases
    · exact ⟨hwrel, hwshort⟩
    · intro j
      exact ⟨hvrel j, hvshort j⟩
  have := P.le_shortRelationRank (Nat.succ_le_of_lt hrd) hfamily
  rw [← hr] at this
  omega

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
    rw [sub_smul, natCast_zsmul, natCast_zsmul, sub_eq_zero]
    exact h
  exact_mod_cast sub_eq_zero.1 ((IsAddTorsionFree.zsmul_eq_zero_iff_left ha).1 h')

/-- Suppose that the multiples `n • a` with `n < N` of every nonzero `a` are distinct, as in a
cyclic group of prime order `N` or in a torsion-free group. The real span of a short independent
family is already made of relations when `N` is large compared with the progression. Otherwise
the first `N` multiples of a nonrelation, reduced into a fundamental parallelepiped, would give
`N` distinct elements in a bounded dilate of the coefficient box. -/
theorem saturatedSpan_shortRelations_le_relations {N r : ℕ} (P : GAP G)
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
    · refine mem_intBox.mpr ?_
      intro i
      have hyi := hy i
      have hL : (0 : ℝ) ≤ (P.halfWidth i : ℝ) := Nat.cast_nonneg _
      have hrdR : (r : ℝ) ≤ P.dim := by exact_mod_cast hrd
      have hmul := mul_le_mul_of_nonneg_right hrdR
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hL)
      have hyr : |(y i : ℝ)| ≤
          (3 * P.dim * P.halfWidth i : ℕ) := by
        push_cast
        nlinarith
      rw [← Int.cast_abs] at hyr
      exact_mod_cast hyr
  choose y hy using hreduce
  let f : Fin N → P.boundedStepImage (3 * P.dim) :=
    fun a ↦ ⟨stepHom P (y a), by
      rw [boundedStepImage, Finset.mem_image]
      exact ⟨y a, hy a |>.2, rfl⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hmap : (a : ℕ) • stepHom P x = (b : ℕ) • stepHom P x := by
      rw [← (hy a).1, ← (hy b).1]
      exact congr_arg Subtype.val hab
    exact Fin.ext (hG _ hxne a.isLt b.isLt hmap)
  have hcard : N ≤ (P.boundedStepImage (3 * P.dim)).card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_le_of_injective f hf
  exact (not_lt_of_ge (hcard.trans (P.card_boundedStepImage_le (3 * P.dim)))) hroom

/-! ### Properness through the short rank -/

/-- A progression with no nonzero relation in the `3`-dilate of its coefficient box is 2-proper: a
relation inside the doubled box has `|vᵢ| ≤ 2 ℓᵢ - 1 ≤ 3 (ℓᵢ - 1)` once every length is at least
two, so it is short for the dilation factor `3`. -/
theorem twoProper_of_shortRelationRank_eq_zero (P : GAP G) (hlen : ∀ i, 2 ≤ P.length i)
    (hrank : P.shortRelationRank 3 = 0) : P.TwoProper := by
  apply P.twoProper_iff.mpr
  intro v hv hlt
  by_contra hne
  obtain ⟨i₀, -⟩ := Function.ne_iff.1 hne
  refine absurd (P.le_shortRelationRank (t := 3) (Nat.succ_le_of_lt i₀.pos)
    ⟨fun _ ↦ v, linearIndependent_unique_iff.mpr hne, fun _ ↦ ⟨hv, ?_⟩⟩) (by grind)
  intro i
  have hlen' : (2 : ℤ) ≤ (P.length i : ℤ) := by exact_mod_cast hlen i
  have hint : |v i| ≤ 3 * ((P.length i : ℤ) - 1) := by
    have := Int.lt_iff_add_one_le.mp (hlt i)
    linarith
  have hcast : ((3 * ((P.length i : ℤ) - 1) : ℤ) : ℝ) = 3 * (P.halfWidth i : ℝ) := by
    rw [P.cast_halfWidth]
    push_cast
    ring
  calc |(v i : ℝ)| = ((|v i| : ℤ) : ℝ) := by rw [Int.cast_abs]
    _ ≤ ((3 * ((P.length i : ℤ) - 1) : ℤ) : ℝ) := by exact_mod_cast hint
    _ = 3 * (P.halfWidth i : ℝ) := hcast

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

/-- The integer points of a saturated projected coefficient box admit a proper centered
reboxing, with the explicit loss produced by the shortest-direction induction. -/
theorem exists_proper_GAP_reboxing_smithQuotientCoords
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
  have hlen := P.length_pos i
  rw [BoxLattice.intCastHom_apply, ← Int.cast_abs]
  exact_mod_cast (show |v i| ≤ (P.halfWidth i : ℤ) by
    rw [halfWidth]
    omega)

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
      ext x
      constructor
      · rintro ⟨w, hw, rfl⟩
        rw [Finset.mem_coe, Finset.mem_image] at hw
        obtain ⟨j, -, rfl⟩ := hw
        exact ⟨j, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨v j, by simp, rfl⟩
    rwa [hset] at hker
  obtain ⟨z, hcongr, hz⟩ := exists_congr_close_isShort v hshort z₀ b hspan
  refine ⟨z, ?_, ?_⟩
  · have hspanSat : Submodule.span ℤ (Set.range v) ≤ saturatedSpan S := by
      apply Submodule.span_le.mpr
      rintro w ⟨j, rfl⟩
      apply subset_saturatedSpan S
      rw [hS, Finset.mem_coe, Finset.mem_image]
      exact ⟨j, Finset.mem_univ _, rfl⟩
    have hmaps := (smithQuotientMap_eq_iff snf z₀ z).mpr (hspanSat hcongr)
    rw [smithQuotientMap_lift] at hmaps
    exact hmaps.symm
  · refine mem_intBox.mpr ?_
    intro i
    have hb' : |b i| ≤ (P.halfWidth i : ℝ) := hb i
    have hz' := hz i
    have hL : (0 : ℝ) ≤ (P.halfWidth i : ℝ) := Nat.cast_nonneg _
    have hreal : |(z i : ℝ)| ≤ ((3 * r + 1) * P.halfWidth i : ℕ) := by
      push_cast
      nlinarith
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
      ext x
      constructor
      · rintro ⟨w, hw, rfl⟩
        rw [Finset.mem_coe, Finset.mem_image] at hw
        obtain ⟨j, -, rfl⟩ := hw
        exact ⟨j, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨v j, by simp, rfl⟩
    rwa [hset] at hker
  obtain ⟨z, hcongr, hz⟩ :=
    exists_congr_close_isShort v hshort z₀ (b - b₀) hspan
  have hspanSat : Submodule.span ℤ (Set.range v) ≤ saturatedSpan S := by
    apply Submodule.span_le.mpr
    rintro w ⟨j, rfl⟩
    apply subset_saturatedSpan S
    rw [hS, Finset.mem_coe, Finset.mem_image]
    exact ⟨j, Finset.mem_univ _, rfl⟩
  have hzmap : smithQuotientMap snf z = y - y₀ := by
    have hmaps := (smithQuotientMap_eq_iff snf z₀ z).mpr (hspanSat hcongr)
    rw [smithQuotientMap_lift] at hmaps
    exact hmaps.symm
  refine ⟨z, ?_, hzmap, ?_⟩
  · change stepHom P z = 0
    rw [← P.stepHom_smithQuotientMap snf hrel z, hzmap, map_sub, himage, sub_self]
  · refine mem_intBox.mpr ?_
    intro i
    have hb' : |b i| ≤ (P.halfWidth i : ℝ) := hb i
    have hb₀' : |b₀ i| ≤ (P.halfWidth i : ℝ) := hb₀ i
    have hz' := hz i
    have hbb₀ : |b i - b₀ i| ≤ 2 * (P.halfWidth i : ℝ) :=
      (abs_sub _ _).trans (by linarith)
    have hbb₀' : |(b - b₀) i| ≤ 2 * (P.halfWidth i : ℝ) := by
      simpa only [Pi.sub_apply] using hbb₀
    have hreal : |(z i : ℝ)| ≤ ((3 * r + 2) * P.halfWidth i : ℕ) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) (P.halfWidth i)]
    rw [← Int.cast_abs] at hreal
    exact_mod_cast hreal

/-- Fibres of the quotient step map on the projected body have dimension-only size. Distinct
representatives are separated by the `3`-box, since every `3`-short relation belongs to the
maximal saturated short span. -/
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
  have hy₀ := (Finset.mem_filter.mp (hF ▸ hy₀F)).1
  have hlift : ∀ y, ∃ z : Fin P.dim → ℤ, y ∈ F →
      z ∈ P.relations ∧ smithQuotientMap snf z = y - y₀ ∧
        z ∈ intBox (fun i ↦ (3 * r + 2) * P.halfWidth i) := by
    intro y
    by_cases hyF : y ∈ F
    swap
    · exact ⟨0, fun h ↦ absurd h hyF⟩
    have hyfilter := Finset.mem_filter.mp (hF ▸ hyF)
    have hy₀filter := Finset.mem_filter.mp (hF ▸ hy₀F)
    obtain ⟨z, hzrel, hzmap, hzbox⟩ :=
      P.exists_bounded_relation_of_same_smithImage v hS hvshort snf hrel
        hyfilter.1 hy₀filter.1 (hyfilter.2.trans hy₀filter.2.symm)
    exact ⟨z, fun _ ↦ ⟨hzrel, hzmap, hzbox⟩⟩
  choose z hz using hlift
  have hzinj : Set.InjOn z F := by
    intro a ha b hb hab
    have hmaps := congr_arg (smithQuotientMap snf) hab
    rw [(hz a ha).2.1, (hz b hb).2.1, sub_left_inj] at hmaps
    exact hmaps
  set Z := F.image z with hZ
  have hZcard : Z.card = F.card := by
    rw [hZ, Finset.card_image_of_injOn hzinj]
  have hbox : ∀ u ∈ Z, ∀ i,
      |u i| ≤ (((3 * r + 2) * P.halfWidth i : ℕ) : ℤ) := by
    intro u hu i
    rw [hZ, Finset.mem_image] at hu
    obtain ⟨y, hyF, rfl⟩ := hu
    exact mem_intBox.mp (hz y hyF).2.2 i
  have hsep : ∀ u ∈ Z, ∀ w ∈ Z, u ≠ w →
      ∃ i, ((3 * P.halfWidth i : ℕ) : ℤ) < |u i - w i| := by
    intro u hu w hw huw
    rw [hZ, Finset.mem_image] at hu hw
    obtain ⟨a, haF, rfl⟩ := hu
    obtain ⟨b, hbF, rfl⟩ := hw
    by_contra! hcon
    have hdiffrel : z a - z b ∈ P.relations :=
      P.relations.sub_mem (hz a haF).1 (hz b hbF).1
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
    rw [(hz a haF).2.1, (hz b hbF).2.1, sub_left_inj] at hmaps
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

/-- The full projected lattice-point set is bounded by a dimension-only factor times the original
progression. This combines the bounded image estimate with the separated-fibre estimate. -/
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
  have himage := P.card_image_smithQuotientCoords_le v hS hvshort snf hrel
  apply (Nat.mul_le_mul_left ((2 * r + 4) ^ P.dim) himage).trans
  rw [← mul_assoc, ← mul_pow]

/-- Reboxing after quotienting by a saturated family of relations gives a
progression whose dimension is the complementary Smith rank. -/
theorem exists_container_of_saturated_relations (P : GAP G) {n : ℕ}
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
      have := hc i
      rw [abs_of_nonneg this.1]
      omega
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

/-- The simultaneous quotient rank-reduction step. All relations below the cutoff are removed at
once, their saturation consists of genuine relations by the room hypothesis, and the projected
body has dimension-only size by `card_smithQuotientCoords_le`. -/
theorem twoProper_or_exists_GAP_dim_lt {N : ℕ} (P : GAP G)
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
  refine Or.inr ⟨Q, hsub, hQdim.trans_lt (by omega), ?_⟩
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

/-- The universal cost constant for iterated properization. -/
def properizationConstant : ℝ := 14

lemma properizationConstant_pos : 0 < properizationConstant := by
  norm_num [properizationConstant]

/-- Iterating the saturated quotient step properizes a progression. The cubic cost of each step
telescopes into a quartic exponent because the dimension decreases strictly.

The group enters through one hypothesis: the multiples `n • a` with `n < N` of every nonzero `a`
are distinct, for some `N` that is large compared with the progression. -/
theorem exists_twoProperGAP_container_of_injOn_nsmul {N : ℕ} (P : GAP G)
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
      let P₂ := P.scaleLengths 2 (by omega)
      have hdim : P₂.dim = d := hdimP
      have hPsub : P.carrier ⊆ P₂.carrier := by
        exact P.carrier_subset_reshape _ (fun i ↦ Nat.mul_pos (by omega) (P.length_pos i))
          fun i ↦ by omega
      have hP₂len : ∀ i, 2 ≤ P₂.length i := by
        intro i
        have hi := P₂.length_pos i
        simp only [P₂, GAP.scaleLengths_length]
        simp only [P₂, GAP.scaleLengths_length] at hi
        omega
      have hP₂cardNat : P₂.carrier.card ≤ 2 ^ d * P.carrier.card := by
        simpa only [P₂, hdimP] using P.card_scaleLengths_le 2 (by omega)
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
          simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hfactor
        have hexp :
            Real.exp (13 * ((d : ℝ) + 2) ^ 3) <
              Real.exp (properizationConstant * ((d : ℝ) + 2) ^ 4) := by
          apply Real.exp_lt_exp.mpr
          have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
          have hx : (1 : ℝ) < (d : ℝ) + 2 := by linarith
          have hpow : ((d : ℝ) + 2) ^ 3 < ((d : ℝ) + 2) ^ 4 := by
            rw [pow_succ]
            nlinarith [pow_pos (show (0 : ℝ) < (d : ℝ) + 2 by positivity) 3]
          rw [properizationConstant]
          nlinarith [pow_pos (show (0 : ℝ) < (d : ℝ) + 2 by positivity) 4]
        have hstrict :
            Real.exp (13 * ((d : ℝ) + 2) ^ 3) * P.carrier.card <
              Real.exp (properizationConstant * ((d : ℝ) + 2) ^ 4) *
                P.carrier.card := by
          exact mul_lt_mul_of_pos_right hexp (by exact_mod_cast P.nonempty.card_pos)
        have hreal :
            (((2 * (3 * d) + 1) ^ d * P₂.carrier.card : ℕ) : ℝ) < (N : ℝ) :=
          hfactorCard.trans_lt (hstrict.trans_le (by simpa only [hdimP] using hroom))
        simpa only [hdim] using (show
          (2 * (3 * d) + 1) ^ d * P₂.carrier.card < N by exact_mod_cast hreal)
      rcases P₂.twoProper_or_exists_GAP_dim_lt hG hP₂len hstepRoom with
        hproper | ⟨Q, hP₂sub, hQdim, hQcard⟩
      · refine ⟨P₂, hproper, hPsub, ?_, hdim.le, ?_⟩
        · intro i
          exact lt_of_lt_of_le (by omega) (hP₂len i)
        · refine hP₂card.trans ?_
          refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (Nat.cast_nonneg _)
          have hA1 : 1 ≤ properizationConstant := by
            norm_num [properizationConstant]
          have hpow : ((d : ℝ) + 2) ^ 3 ≤ ((d : ℝ) + 2) ^ 4 := by
            rw [pow_succ]
            nlinarith [pow_nonneg (show (0 : ℝ) ≤ (d : ℝ) + 2 by positivity) 3]
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
          rw [hdim, ← mul_assoc, ← Real.exp_add]
          rw [properizationConstant]
          congr 1
          ring_nf
        have hQroom :
            Real.exp (properizationConstant * ((Q.dim : ℝ) + 2) ^ 4) *
                Q.carrier.card ≤ N := by
          apply (mul_le_mul_of_nonneg_left hQcard' (by positivity)).trans
          rw [← mul_assoc, ← Real.exp_add]
          refine (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_)
            (Nat.cast_nonneg _)).trans hroom
          simpa only [hdim, hdimP] using
            cube_step_le_fourth_difference properizationConstant_pos.le hQdim
        obtain ⟨R, hRproper, hQRsub, hRlen, hRdim, hRcard⟩ :=
          ih Q.dim (by simpa only [hdim] using hQdim) Q hQroom rfl
        refine ⟨R, hRproper, hPsub.trans (hP₂sub.trans hQRsub), hRlen,
          hRdim.trans (Nat.le_of_lt (by simpa only [hdim] using hQdim)), ?_⟩
        apply hRcard.trans
        apply (mul_le_mul_of_nonneg_left hQcard' (by positivity)).trans
        rw [← mul_assoc, ← Real.exp_add]
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (Nat.cast_nonneg _)
        simpa only [hdim, hdimP] using
          cube_step_le_fourth_difference properizationConstant_pos.le hQdim

/-- Properization in `ZMod q` for a prime `q` that is large compared with the progression. -/
theorem exists_twoProperGAP_container {q : ℕ} (P : GAP (ZMod q))
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

/-- Properization in a torsion-free group, for instance in `ℤ`. No room is needed. -/
theorem exists_twoProperGAP_container_of_isAddTorsionFree [IsAddTorsionFree G] (P : GAP G) :
    ∃ Q : GAP G, Q.TwoProper ∧ P.carrier ⊆ Q.carrier ∧
      (∀ i, 1 < Q.length i) ∧ Q.dim ≤ P.dim ∧
      (Q.carrier.card : ℝ) ≤
        Real.exp (properizationConstant * ((P.dim : ℝ) + 2) ^ 4) *
          P.carrier.card :=
  exists_twoProperGAP_container_of_injOn_nsmul P
    (fun _ ha ↦ GAP.injOn_nsmul_of_isAddTorsionFree _ ha) (Nat.le_ceil _)

end

end ChangFreimanRuzsa
