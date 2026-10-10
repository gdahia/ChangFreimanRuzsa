/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup

/-! # Successive minima of a lattice with respect to a symmetric convex body

This file develops the successive minima of a discrete subgroup of a real normed space with respect
to a symmetric convex body, in the generality required by the reboxing step of properization. It is
the real counterpart of `Chang.GeometryOfNumbers`, which does the same for a box of integer points.

The main pieces are:

- `setOf_mem_smul_eq_Ici` and `mem_smul_iff_gauge_le`, which identify the dilation factors whose
  dilate of `K` contains a given point with the closed half-line above its gauge. Everything else
  rests on this: it is what makes the minima behave like minima rather than like infima;
- `successiveMinimum`, the `k`-th successive minimum, with its basic API;
- `le_successiveMinimum_one`, positivity of the first minimum, from discreteness of the lattice;
- `exists_witness_successiveMinimum`, attainment of the infimum defining the minima;
- `exists_intCast_smul_eq_of_gauge_min` and `gauge_le_two_mul_of_mem_map`, the steps of the
  projection along a shortest lattice vector: a shortest vector is primitive, and the first minimum
  of the lattice is at most twice the gauge of any nonzero vector of the projected lattice;
- `convex_image`, `neg_mem_image`, `exists_pos_forall_norm_apply_lt` and
  `discreteTopology_of_exists_pos_forall_norm_lt`, which say that the projected body is a symmetric
  convex set and the projected lattice a discrete subgroup again.

`Chang.Reboxing.GaugeInduction` assembles these into the shortest-direction induction.
-/

@[expose] public section

namespace ChangFreimanRuzsa

namespace ConvexGeometry

open scoped Pointwise Topology

open Metric Module

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E}

/-! ## Dilates of a convex body

A symmetric convex body is a closed, bounded, convex neighbourhood of the origin. For such a body
the gauge decides which dilates contain a given point. -/

/-- The dilation factors whose dilate of `K` contains `x` form the closed half-line above the gauge
of `x`. -/
lemma setOf_mem_smul_eq_Ici (hconv : Convex ℝ K) (hclosed : IsClosed K) (hK₀ : K ∈ 𝓝 0)
    (hbdd : Bornology.IsVonNBounded ℝ K) (x : E) :
    {t : ℝ | 0 ≤ t ∧ x ∈ t • K} = Set.Ici (gauge K x) := by
  apply Set.ext
  intro t
  constructor
  · intro ht
    exact gauge_le_of_mem ht.1 ht.2
  · intro ht
    refine ⟨(gauge_nonneg x).trans ht, ?_⟩
    rcases eq_or_ne x 0 with rfl | hx
    · rw [← smul_zero t]
      exact Set.smul_mem_smul_set (mem_of_mem_nhds hK₀)
    · have htpos : 0 < t :=
        lt_of_lt_of_le ((gauge_pos (absorbent_nhds_zero hK₀) hbdd).mpr hx) ht
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ htpos.ne', ← hclosed.closure_eq,
        ← gauge_le_one_iff_mem_closure hconv hK₀, gauge_smul_of_nonneg (inv_nonneg.mpr htpos.le),
        smul_eq_mul, inv_mul_le_one₀ htpos]
      exact ht

/-- Membership in a dilate of a convex body is decided by the gauge. -/
lemma mem_smul_iff_gauge_le (hconv : Convex ℝ K) (hclosed : IsClosed K) (hK₀ : K ∈ 𝓝 0)
    (hbdd : Bornology.IsVonNBounded ℝ K) {t : ℝ} (ht : 0 ≤ t) (x : E) :
    x ∈ t • K ↔ gauge K x ≤ t := by
  constructor
  · exact gauge_le_of_mem ht
  · intro h
    have hmem : t ∈ {t : ℝ | 0 ≤ t ∧ x ∈ t • K} := by
      rw [setOf_mem_smul_eq_Ici hconv hclosed hK₀ hbdd]
      exact h
    exact hmem.2

/-- Membership in a dilate is monotone in the dilation factor. -/
lemma mem_smul_of_le (hconv : Convex ℝ K) (hclosed : IsClosed K) (hK₀ : K ∈ 𝓝 0)
    (hbdd : Bornology.IsVonNBounded ℝ K) {x : E} {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hx : x ∈ s • K) : x ∈ t • K :=
  (mem_smul_iff_gauge_le hconv hclosed hK₀ hbdd (hs.trans hst) x).mpr
    (le_trans ((mem_smul_iff_gauge_le hconv hclosed hK₀ hbdd hs x).mp hx) hst)

/-! ## Successive minima -/

/-- `HasIndependentShort L K k t` says that the `t`-dilate of `K` contains `k` linearly independent
vectors of `L`. -/
def HasIndependentShort (L : AddSubgroup E) (K : Set E) (k : ℕ) (t : ℝ) : Prop :=
  ∃ v : Fin k → E, LinearIndependent ℝ v ∧ ∀ j, v j ∈ L ∧ v j ∈ t • K

/-- The `k`-th successive minimum of `L` with respect to `K`: the least dilation factor of `K`
whose points contain `k` linearly independent vectors of `L`. -/
def successiveMinimum (L : AddSubgroup E) (K : Set E) (k : ℕ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ HasIndependentShort L K k t}

variable {L : AddSubgroup E} {k : ℕ}

lemma bddBelow_dilations (L : AddSubgroup E) (K : Set E) (k : ℕ) :
    BddBelow {t : ℝ | 0 ≤ t ∧ HasIndependentShort L K k t} :=
  ⟨0, fun _ ht ↦ ht.1⟩

lemma successiveMinimum_nonneg (L : AddSubgroup E) (K : Set E) (k : ℕ) :
    0 ≤ successiveMinimum L K k :=
  Real.sInf_nonneg fun _ ht ↦ ht.1

/-- Any dilation factor carrying `k` independent lattice vectors bounds the `k`-th minimum. -/
lemma successiveMinimum_le {t : ℝ} (ht : 0 ≤ t) (h : HasIndependentShort L K k t) :
    successiveMinimum L K k ≤ t :=
  csInf_le (bddBelow_dilations L K k) ⟨ht, h⟩

/-- A dilation factor below every one that carries `k` independent lattice vectors is below the
`k`-th minimum. -/
lemma le_successiveMinimum {t : ℝ} (hne : ∃ s, 0 ≤ s ∧ HasIndependentShort L K k s)
    (h : ∀ s, 0 ≤ s → HasIndependentShort L K k s → t ≤ s) : t ≤ successiveMinimum L K k :=
  le_csInf hne fun s hs ↦ h s hs.1 hs.2

/-! ## Positivity of the first minimum -/

omit [NormedSpace ℝ E] in
/-- A discrete subgroup meets a small enough ball around the origin only at the origin. -/
lemma exists_pos_forall_norm_lt (L : AddSubgroup E) [DiscreteTopology L] :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ L, ‖x‖ < r → x = 0 := by
  obtain ⟨U, hUopen, hUL⟩ :=
    isOpen_inter_eq_singleton_of_mem_discrete (s := (L : Set E)) DiscreteTopology.isDiscrete
      (zero_mem L)
  have h0U : (0 : E) ∈ U ∩ (L : Set E) := by
    rw [hUL]
    exact Set.mem_singleton 0
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hUopen 0 h0U.1
  refine ⟨r, hr, ?_⟩
  intro x hx hnorm
  have hxU : x ∈ U ∩ (L : Set E) :=
    ⟨hball (by simpa only [Metric.mem_ball, dist_zero_right] using hnorm), hx⟩
  rw [hUL] at hxU
  exact hxU

/-- The first minimum is positive: a dilation factor whose dilate of `K` stays inside a ball that
the lattice meets only at the origin is below it. -/
lemma le_successiveMinimum_one [DiscreteTopology L] {R r t : ℝ} (hR : K ⊆ closedBall 0 R)
    (hr : ∀ x ∈ L, ‖x‖ < r → x = 0) (ht : 0 ≤ t) (htR : t * R < r)
    (hne : ∃ s, 0 ≤ s ∧ HasIndependentShort L K 1 s) : t ≤ successiveMinimum L K 1 := by
  apply le_successiveMinimum hne
  intro s hs hshort
  by_contra! hlt
  obtain ⟨v, hindep, hv⟩ := hshort
  obtain ⟨y, hy, hyv⟩ := (hv 0).2
  refine hindep.ne_zero 0 (hr _ (hv 0).1 ?_)
  rw [← hyv, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
  have hyR : ‖y‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hR hy
  nlinarith [norm_nonneg y]

/-! ## Attainment of the minima -/

/-- The lattice points inside a dilate of a bounded body form a finite set. -/
lemma finite_lattice_inter_smul [ProperSpace E] (L : AddSubgroup E) [DiscreteTopology L]
    (hbdd : Bornology.IsBounded K) (t : ℝ) : Set.Finite (t • K ∩ (L : Set E)) :=
  Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
    (Bornology.IsBounded.smul₀ hbdd t) AddSubgroup.isClosed_of_discreteTopology

/-- The infimum defining a successive minimum is attained: some family of `k` independent vectors
of `L` lies in the dilate of `K` by `successiveMinimum L K k` itself.

Discreteness bounds the number of candidate families, and `setOf_mem_smul_eq_Ici` turns each
family's set of admissible dilation factors into a closed half-line, so the infimum lies in a
finite union of closed half-lines. -/
theorem exists_witness_successiveMinimum [ProperSpace E] [DiscreteTopology L]
    (hconv : Convex ℝ K) (hclosed : IsClosed K) (hK₀ : K ∈ 𝓝 0) (hbdd : Bornology.IsBounded K)
    (hne : ∃ t, 0 ≤ t ∧ HasIndependentShort L K k t) :
    HasIndependentShort L K k (successiveMinimum L K k) := by
  classical
  set T := {t : ℝ | 0 ≤ t ∧ HasIndependentShort L K k t} with hT
  set lam := successiveMinimum L K k with hlam
  have hTne : T.Nonempty := by
    obtain ⟨t, ht⟩ := hne
    exact ⟨t, ht⟩
  have hvonN : Bornology.IsVonNBounded ℝ K := (NormedSpace.isVonNBounded_iff ℝ).mpr hbdd
  set Fams := {v : Fin k → E |
    (∀ j, v j ∈ (lam + 1) • K ∩ (L : Set E)) ∧ LinearIndependent ℝ v} with hFams
  have hFamsfin : Fams.Finite :=
    Set.Finite.subset (Set.Finite.pi fun _ ↦ finite_lattice_inter_smul L hbdd (lam + 1))
      fun v hv ↦ Set.mem_univ_pi.mpr hv.1
  have hsub : T ⊆ (⋃ v ∈ Fams, ⋂ j, Set.Ici (gauge K (v j))) ∪ Set.Ici (lam + 1) := by
    intro t ht
    rcases le_or_gt (lam + 1) t with hle | hlt
    · exact Or.inr hle
    obtain ⟨v, hindep, hv⟩ := ht.2
    refine Or.inl (Set.mem_iUnion₂.mpr ⟨v, ?_, ?_⟩)
    · constructor
      · intro j
        constructor
        · exact mem_smul_of_le hconv hclosed hK₀ hvonN ht.1 hlt.le (hv j).2
        · exact (hv j).1
      · exact hindep
    · exact Set.mem_iInter.mpr fun j ↦
        (mem_smul_iff_gauge_le hconv hclosed hK₀ hvonN ht.1 (v j)).mp (hv j).2
  have hmem : lam ∈ (⋃ v ∈ Fams, ⋂ j, Set.Ici (gauge K (v j))) ∪ Set.Ici (lam + 1) :=
    ((hFamsfin.isClosed_biUnion fun _ _ ↦
      isClosed_iInter fun _ ↦ isClosed_Ici).union isClosed_Ici).closure_subset_iff.mpr hsub
      ((Real.isGLB_sInf hTne (bddBelow_dilations L K k)).mem_closure hTne)
  obtain hmem | hmem := hmem
  · obtain ⟨v, hv, hvlam⟩ := Set.mem_iUnion₂.mp hmem
    exact ⟨v, hv.2, fun j ↦ ⟨(hv.1 j).2, (mem_smul_iff_gauge_le hconv hclosed hK₀ hvonN
      (successiveMinimum_nonneg L K k) (v j)).mpr (Set.mem_iInter.mp hvlam j)⟩⟩
  · exact absurd (Set.mem_Ici.mp hmem) (not_le.mpr (by linarith))

/-! ## Projecting along a shortest lattice vector

The elementary steps of the shortest-direction induction of `Chang.Reboxing.GaugeInduction`. They
use no measure theory: only the body and its gauge enter. -/

/-- The gauge of a symmetric body does not see signs. -/
lemma gauge_smul_abs (hsymm : ∀ x ∈ K, -x ∈ K) (m : ℝ) (x : E) :
    gauge K (m • x) = |m| * gauge K x := by
  rcases le_or_gt 0 m with hm | hm
  · rw [gauge_smul_of_nonneg hm, smul_eq_mul, abs_of_nonneg hm]
  · rw [← gauge_neg hsymm, ← neg_smul, gauge_smul_of_nonneg (by linarith : (0 : ℝ) ≤ -m),
      smul_eq_mul, abs_of_neg hm]

lemma gauge_zsmul_le (hsymm : ∀ x ∈ K, -x ∈ K) (m : ℝ) (x : E) :
    gauge K (m • x) ≤ |m| * gauge K x := (gauge_smul_abs hsymm m x).le

/-- Reduction along a lattice direction: a point differing from a point of gauge at most `t` by a
real multiple of `v` can be moved by an *integer* multiple of `v` to a point of gauge at most
`t + gauge K v / 2`.

This is the step that compares the successive minima of a quotient lattice with those of the
lattice itself: applied with `v` a shortest vector, it shows that a short vector of the quotient
lifts to a lattice vector that is short by at most `λ₁ / 2`. -/
lemma exists_int_gauge_sub_zsmul_le (hconv : Convex ℝ K) (hK₀ : K ∈ 𝓝 0)
    (hsymm : ∀ x ∈ K, -x ∈ K) {t : ℝ} {y z v : E} {s : ℝ} (hz : gauge K z ≤ t)
    (hy : y = z + s • v) : ∃ m : ℤ, gauge K (y - (m : ℝ) • v) ≤ t + gauge K v / 2 := by
  use round s
  rw [hy, add_sub_assoc, ← sub_smul]
  apply le_trans (gauge_add_le hconv (absorbent_nhds_zero hK₀) _ _)
  refine add_le_add hz (le_trans (gauge_zsmul_le hsymm _ _) ?_)
  rw [div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_right ?_ (gauge_nonneg v)
  simpa only [one_div] using abs_sub_round s

/-- A nonzero lattice vector of least gauge is primitive: every lattice point on its line is an
integer multiple of it.

This is the step of the induction that lets the projection along `v` carry the lattice to a
lattice. -/
lemma exists_intCast_smul_eq_of_gauge_min (hsymm : ∀ x ∈ K, -x ∈ K) {v w : E} (hv : v ∈ L)
    (hvpos : 0 < gauge K v) (hmin : ∀ y ∈ L, y ≠ 0 → gauge K v ≤ gauge K y) (hw : w ∈ L)
    {s : ℝ} (hws : w = s • v) : ∃ m : ℤ, w = (m : ℝ) • v := by
  use round s
  by_contra hne
  refine absurd (hmin _ (L.sub_mem hw ?_) (sub_ne_zero_of_ne hne)) (not_le.mpr ?_)
  · rw [Int.cast_smul_eq_zsmul]
    exact L.zsmul_mem hv _
  · rw [hws, ← sub_smul]
    apply lt_of_le_of_lt (gauge_zsmul_le hsymm _ _)
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right (abs_sub_round s) (gauge_nonneg v))
    rw [one_div]
    linarith

/-- **Lifting a single short vector.** A vector of the projected lattice inside the `t`-dilate of
the projected body lifts to a lattice vector of gauge at most `t + gauge K v / 2`: any lift differs
from a point of the `t`-dilate by a multiple of `v`, and rounding that multiple costs
`gauge K v / 2`. -/
lemma exists_mem_gauge_le_of_mem_map {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hconv : Convex ℝ K) (hK₀ : K ∈ 𝓝 0) (hsymm : ∀ x ∈ K, -x ∈ K) (π : E →ₗ[ℝ] F) {v : E}
    (hv : v ∈ L) (hπv : π v = 0) (hker : ∀ x : E, π x = 0 → ∃ s : ℝ, x = s • v) {t : ℝ}
    (ht : 0 ≤ t) {w : F} (hwL : w ∈ L.map (π : E →+ F)) (hwK : w ∈ t • (π '' K)) :
    ∃ y, y ∈ L ∧ π y = w ∧ gauge K y ≤ t + gauge K v / 2 := by
  obtain ⟨y, hyL, hyw⟩ := AddSubgroup.mem_map.mp hwL
  obtain ⟨p, ⟨x, hxK, hxp⟩, hpw⟩ := hwK
  simp only at hpw
  have hkerx : π (y - t • x) = 0 := by
    rw [map_sub, map_smul, hxp, sub_eq_zero]
    exact hyw.trans hpw.symm
  obtain ⟨s, hs⟩ := hker _ hkerx
  obtain ⟨m, hm⟩ := exists_int_gauge_sub_zsmul_le hconv hK₀ hsymm
    (gauge_le_of_mem ht (Set.smul_mem_smul_set hxK)) (sub_eq_iff_eq_add'.mp hs)
  refine ⟨y - (m : ℝ) • v, L.sub_mem hyL ?_, ?_, hm⟩
  · rw [Int.cast_smul_eq_zsmul]
    exact L.zsmul_mem hv _
  · rw [map_sub, map_smul, hπv, smul_zero, sub_zero]
    exact hyw

/-- A nonzero vector of the projected lattice is at least half as long as the shortest lattice
vector: its lift is a nonzero lattice vector of gauge at most `t + gauge K v / 2`.

This compares the first minimum of the lattice with the minima of the projected lattice. -/
lemma gauge_le_two_mul_of_mem_map {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hconv : Convex ℝ K) (hK₀ : K ∈ 𝓝 0) (hsymm : ∀ x ∈ K, -x ∈ K) (π : E →ₗ[ℝ] F) {v : E}
    (hv : v ∈ L) (hπv : π v = 0) (hker : ∀ x : E, π x = 0 → ∃ s : ℝ, x = s • v)
    (hmin : ∀ y ∈ L, y ≠ 0 → gauge K v ≤ gauge K y) {t : ℝ} (ht : 0 ≤ t)
    (h : HasIndependentShort (L.map (π : E →+ F)) (π '' K) 1 t) : gauge K v ≤ 2 * t := by
  obtain ⟨w, hwindep, hw⟩ := h
  obtain ⟨y, hyL, hyπ, hygauge⟩ :=
    exists_mem_gauge_le_of_mem_map hconv hK₀ hsymm π hv hπv hker ht (hw 0).1 (hw 0).2
  have hyne : y ≠ 0 := fun hzero ↦ hwindep.ne_zero 0 (by rw [← hyπ, hzero, map_zero])
  have := hmin y hyL hyne
  linarith

/-! ### The projected body

The induction applies its hypothesis to the image of `K` under the projection, so that image has to
be a symmetric convex set again. -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma convex_image (hconv : Convex ℝ K) (π : E →ₗ[ℝ] F) : Convex ℝ (π '' K) :=
  hconv.linear_image π

lemma neg_mem_image (hsymm : ∀ x ∈ K, -x ∈ K) (π : E →ₗ[ℝ] F) :
    ∀ y ∈ π '' K, -y ∈ π '' K := by
  rintro y ⟨x, hx, rfl⟩
  exact ⟨-x, hsymm x hx, map_neg π x⟩

/-- **Discreteness of the projected lattice.** If a projection `p` kills a lattice vector `v` and
splits every vector as its image plus a multiple of `v`, then the images of the lattice avoid a ball
around the origin.

Reducing modulo `ℤv` moves a lattice vector with small image into a fixed bounded set, which meets
the lattice in finitely many points, so only finitely many images are in play. -/
theorem exists_pos_forall_norm_apply_lt [ProperSpace E] [DiscreteTopology L] (p : E →ₗ[ℝ] E)
    {v : E} (hv : v ∈ L) (hpv : p v = 0) (hsplit : ∀ y : E, ∃ s : ℝ, y - p y = s • v) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ L, ‖p y‖ < r → p y = 0 := by
  classical
  have hAfin : (closedBall (0 : E) (‖v‖ + 1) ∩ (L : Set E)).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete isBounded_closedBall
      AddSubgroup.isClosed_of_discreteTopology
  set N := (hAfin.toFinset.image fun y ↦ ‖p y‖).filter (0 < ·) with hN
  refine ⟨if hne : N.Nonempty then min (N.min' hne) 1 else 1, ?_, ?_⟩
  · split
    · exact lt_min (Finset.mem_filter.mp (N.min'_mem _)).2 one_pos
    · exact one_pos
  · intro y hy hylt
    by_contra hpy
    obtain ⟨s, hs⟩ := hsplit y
    have hyv : y - (round s : ℝ) • v ∈ closedBall (0 : E) (‖v‖ + 1) ∩ (L : Set E) := by
      constructor
      · have hrw : y - (round s : ℝ) • v = p y + (s - (round s : ℝ)) • v := by
          rw [sub_smul, ← hs]
          abel
        rw [mem_closedBall, dist_zero_right, hrw]
        apply le_trans (norm_add_le _ _)
        rw [norm_smul, Real.norm_eq_abs]
        have hround := abs_sub_round s
        have hrle : ‖p y‖ ≤ 1 := by
          apply le_trans hylt.le
          split
          · exact min_le_right _ _
          · exact le_rfl
        nlinarith [norm_nonneg v, norm_nonneg (p y)]
      · rw [Int.cast_smul_eq_zsmul]
        exact L.sub_mem hy (L.zsmul_mem hv _)
    have hpeq : p (y - (round s : ℝ) • v) = p y := by
      rw [map_sub, map_smul, hpv, smul_zero, sub_zero]
    have hmemN : ‖p y‖ ∈ N := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨_, ?_, congrArg norm hpeq⟩, ?_⟩
      · exact hAfin.mem_toFinset.mpr hyv
      · exact norm_pos_iff.mpr hpy
    refine absurd hylt (not_lt.mpr ?_)
    rw [dite_eq_left ⟨_, hmemN⟩]
    exact min_le_of_left_le (N.min'_le _ hmemN)

omit [NormedSpace ℝ E] in
/-- Conversely, a subgroup that avoids a ball around the origin is discrete. Together with
`exists_pos_forall_norm_apply_lt` this feeds the projected lattice back into the induction, whose
hypotheses are stated with `DiscreteTopology`. -/
lemma discreteTopology_of_exists_pos_forall_norm_lt {G : AddSubgroup E}
    (h : ∃ r : ℝ, 0 < r ∧ ∀ x ∈ G, ‖x‖ < r → x = 0) : DiscreteTopology G := by
  obtain ⟨r, hr, hG⟩ := h
  rw [discreteTopology_iff_isOpen_singleton_zero]
  refine isOpen_induced_iff.mpr ⟨Metric.ball (0 : E) r, Metric.isOpen_ball, ?_⟩
  apply Set.ext
  intro x
  simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, Set.mem_singleton_iff]
  constructor
  · intro hx
    exact Subtype.ext (hG x x.2 hx)
  · intro hx
    rw [hx]
    simpa using hr

end

end ConvexGeometry

end ChangFreimanRuzsa
