/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Shortest lattice vectors with respect to a symmetric convex body

Let $K$ be a closed bounded convex neighbourhood of the origin in a real normed space $E$, let
$g_K$ be its gauge, and let $L$ be a discrete subgroup of $E$. This file proves the facts about
$g_K$ and $L$ that the induction along shortest lattice vectors in
`ChangFreimanRuzsa.LatticeBox.GaugeInduction` uses. They involve only the body and its gauge, and no
measure theory.

## Main statements

- `mem_smul_iff_gauge_le`: for $t \ge 0$, $x \in tK$ if and only if $g_K(x) \le t$.
- `exists_mem_ne_zero_forall_gauge_le`: a nonzero discrete subgroup has a nonzero vector of least
  gauge.
- `exists_intCast_smul_eq_of_gauge_min`: a nonzero lattice vector of least gauge is primitive.
- `exists_mem_gauge_le_of_mem_map` and `gauge_le_two_mul_of_mem_map`: let $\pi$ be a linear map
  with kernel $\mathbb{R} v$ for a shortest lattice vector $v$. A vector of $\pi(L) \cap t \pi(K)$
  lifts to a vector of $L$ of gauge at most $t + g_K(v) / 2$, and if it is nonzero, then
  $g_K(v) \le 2t$.
- `neg_mem_image` and `exists_pos_forall_le_norm_apply`: the projected body is symmetric, and the
  nonzero projected lattice vectors have norm bounded below.
-/

public section

namespace ChangFreimanRuzsa

namespace ConvexGeometry

open scoped Pointwise Topology

open Metric

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {L : AddSubgroup E}

/-! ## Dilates of a convex body -/

/-- For $t \ge 0$, a point $x$ lies in the dilate $tK$ of a closed bounded convex neighbourhood $K$
of the origin if and only if $g_K(x) \le t$. -/
lemma mem_smul_iff_gauge_le (hconv : Convex ℝ K) (hclosed : IsClosed K) (hK₀ : K ∈ 𝓝 0)
    (hbdd : Bornology.IsVonNBounded ℝ K) {t : ℝ} (ht : 0 ≤ t) (x : E) :
    x ∈ t • K ↔ gauge K x ≤ t := by
  refine ⟨gauge_le_of_mem ht, ?_⟩
  intro hx
  obtain rfl | htpos := ht.eq_or_lt
  · rw [(gauge_eq_zero (absorbent_nhds_zero hK₀) hbdd).mp (hx.antisymm (gauge_nonneg x))]
    exact Set.zero_mem_smul_set (mem_of_mem_nhds hK₀)
  · rwa [Set.mem_smul_set_iff_inv_smul_mem₀ htpos.ne', ← hclosed.closure_eq,
      ← gauge_le_one_iff_mem_closure hconv hK₀, gauge_smul_of_nonneg (inv_nonneg.mpr ht),
      smul_eq_mul, inv_mul_le_one₀ htpos]

/-! ## Shortest lattice vectors -/

/-- A discrete subgroup $L \ne 0$ of a proper space has a nonzero vector of least gauge with respect
to a closed bounded convex neighbourhood $K$ of the origin. For a nonzero $x \in L$, the nonzero
vectors of $L \cap g_K(x) K$ form a finite set, and a vector of least gauge in it has least gauge in
$L \setminus \{0\}$. -/
lemma exists_mem_ne_zero_forall_gauge_le [ProperSpace E] [DiscreteTopology L] (hconv : Convex ℝ K)
    (hclosed : IsClosed K) (hK₀ : K ∈ 𝓝 0) (hbdd : Bornology.IsBounded K) {x : E} (hxL : x ∈ L)
    (hx : x ≠ 0) : ∃ v ∈ L, v ≠ 0 ∧ ∀ y ∈ L, y ≠ 0 → gauge K v ≤ gauge K y := by
  have hmem := mem_smul_iff_gauge_le hconv hclosed hK₀
    ((NormedSpace.isVonNBounded_iff ℝ).mpr hbdd) (gauge_nonneg (s := K) x)
  have hxS : x ∈ (gauge K x • K ∩ L) \ {0} := ⟨⟨(hmem x).mpr le_rfl, hxL⟩, hx⟩
  obtain ⟨v, ⟨⟨-, hvL⟩, hv⟩, hmin⟩ := Set.exists_min_image _ (gauge K)
    (finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete (hbdd.smul₀ _)
      AddSubgroup.isClosed_of_discreteTopology).sdiff ⟨x, hxS⟩
  refine ⟨v, hvL, hv, ?_⟩
  intro y hyL hy
  by_cases hyK : y ∈ gauge K x • K
  · exact hmin y ⟨⟨hyK, hyL⟩, hy⟩
  · exact (hmin x hxS).trans (not_le.mp (hyK ∘ (hmem y).mpr)).le

/-- Rounding along a lattice direction: a point differing from a point of gauge at most $t$ by a
real multiple of $v$ can be moved by an integer multiple of $v$ to a point of gauge at most
$t + g_K(v) / 2$. -/
lemma exists_int_gauge_sub_intCast_smul_le (hconv : Convex ℝ K) (hK₀ : K ∈ 𝓝 0)
    (hsymm : ∀ x ∈ K, -x ∈ K) {s t : ℝ} {y z v : E} (hz : gauge K z ≤ t)
    (hy : y = z + s • v) : ∃ m : ℤ, gauge K (y - (m : ℝ) • v) ≤ t + gauge K v / 2 := by
  use round s
  rw [hy, add_sub_assoc, ← sub_smul]
  refine (gauge_add_le hconv (absorbent_nhds_zero hK₀) _ _).trans (add_le_add hz ?_)
  rw [gauge_smul ((balanced_iff_neg_mem hconv).mpr hsymm), Real.norm_eq_abs, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_right (by simpa using abs_sub_round s) (gauge_nonneg v)

/-- A nonzero lattice vector of least gauge is primitive: every lattice point on its line is an
integer multiple of it. -/
lemma exists_intCast_smul_eq_of_gauge_min (hconv : Convex ℝ K) (hsymm : ∀ x ∈ K, -x ∈ K)
    {v w : E} (hv : v ∈ L) (hvpos : 0 < gauge K v)
    (hmin : ∀ y ∈ L, y ≠ 0 → gauge K v ≤ gauge K y) (hw : w ∈ L) {s : ℝ} (hws : w = s • v) :
    ∃ m : ℤ, w = (m : ℝ) • v := by
  use round s
  by_contra hne
  refine (hmin _ (L.sub_mem hw ?_) (sub_ne_zero_of_ne hne)).not_gt ?_
  · rw [Int.cast_smul_eq_zsmul]
    exact L.zsmul_mem hv _
  · rw [hws, ← sub_smul, gauge_smul ((balanced_iff_neg_mem hconv).mpr hsymm), Real.norm_eq_abs]
    linarith [mul_le_mul_of_nonneg_right (abs_sub_round s) hvpos.le]

/-! ## Projecting along a shortest lattice vector -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Let $\pi$ be a linear map with kernel $\mathbb{R} v$ for some $v \in L$. A vector of $\pi(L)$
in the dilate $t \pi(K)$ lifts to a vector of $L$ of gauge at most $t + g_K(v) / 2$. Any lift
differs from a point of $tK$ by a multiple of $v$, and rounding that multiple adds at most
$g_K(v) / 2$. -/
lemma exists_mem_gauge_le_of_mem_map (hconv : Convex ℝ K) (hK₀ : K ∈ 𝓝 0)
    (hsymm : ∀ x ∈ K, -x ∈ K) {π : E →ₗ[ℝ] F} {v : E} (hv : v ∈ L) (hπv : π v = 0)
    (hker : ∀ x, π x = 0 → ∃ s : ℝ, x = s • v) {t : ℝ} (ht : 0 ≤ t) {w : F}
    (hwL : w ∈ L.map (π : E →+ F)) (hwK : w ∈ t • π '' K) :
    ∃ y ∈ L, π y = w ∧ gauge K y ≤ t + gauge K v / 2 := by
  obtain ⟨y, hyL, rfl⟩ := AddSubgroup.mem_map.mp hwL
  obtain ⟨_, ⟨x, hxK, rfl⟩, hxy⟩ := hwK
  obtain ⟨s, hs⟩ := hker (y - t • x) (by simpa [sub_eq_zero] using hxy.symm)
  obtain ⟨m, hm⟩ := exists_int_gauge_sub_intCast_smul_le hconv hK₀ hsymm
    (gauge_le_of_mem ht (Set.smul_mem_smul_set hxK)) (sub_eq_iff_eq_add'.mp hs)
  refine ⟨y - (m : ℝ) • v, L.sub_mem hyL ?_, by simp [hπv], hm⟩
  rw [Int.cast_smul_eq_zsmul]
  exact L.zsmul_mem hv _

/-- Let $\pi$ be a linear map with kernel $\mathbb{R} v$ for a nonzero vector $v \in L$ of least
gauge. If a nonzero vector of $\pi(L)$ lies in $t \pi(K)$, then $g_K(v) \le 2t$, since its lift is
a nonzero vector of $L$ of gauge at most $t + g_K(v) / 2$. -/
lemma gauge_le_two_mul_of_mem_map (hconv : Convex ℝ K) (hK₀ : K ∈ 𝓝 0)
    (hsymm : ∀ x ∈ K, -x ∈ K) {π : E →ₗ[ℝ] F} {v : E} (hv : v ∈ L) (hπv : π v = 0)
    (hker : ∀ x, π x = 0 → ∃ s : ℝ, x = s • v) (hmin : ∀ y ∈ L, y ≠ 0 → gauge K v ≤ gauge K y)
    {t : ℝ} (ht : 0 ≤ t) {w : F} (hwL : w ∈ L.map (π : E →+ F)) (hw : w ≠ 0)
    (hwK : w ∈ t • π '' K) : gauge K v ≤ 2 * t := by
  obtain ⟨y, hyL, rfl, hy⟩ := exists_mem_gauge_le_of_mem_map hconv hK₀ hsymm hv hπv hker ht hwL hwK
  linarith [hmin y hyL (ne_of_apply_ne π (by simpa using hw))]

/-- The image of a symmetric set under a linear map is symmetric. -/
lemma neg_mem_image (hsymm : ∀ x ∈ K, -x ∈ K) {π : E →ₗ[ℝ] F} ⦃y : F⦄ (hy : y ∈ π '' K) :
    -y ∈ π '' K := by
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨-x, hsymm x hx, map_neg π x⟩

/-- Let $p$ be a linear map with $p(v) = 0$ for some $v \in L$ and $y - p(y) \in \mathbb{R} v$ for
every $y$. Then the norms of the nonzero vectors of $p(L)$ are bounded below by a positive constant.

Subtracting the nearest integer multiple of $v$ moves a vector $y \in L$ with $\|p(y)\| \le 1$ into
the ball of radius $\|v\| + 1$ without changing $p(y)$, and that ball meets $L$ in finitely many
points. -/
lemma exists_pos_forall_le_norm_apply [ProperSpace E] [DiscreteTopology L] {p : E →ₗ[ℝ] E}
    {v : E} (hv : v ∈ L) (hpv : p v = 0) (hsplit : ∀ y, ∃ s : ℝ, y - p y = s • v) :
    ∃ r, 0 < r ∧ ∀ y ∈ L, p y ≠ 0 → r ≤ ‖p y‖ := by
  obtain ⟨ε, hε, hball⟩ := exists_ball_inter_eq_singleton_of_mem_discrete
    ((finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      (isBounded_closedBall (x := 0) (r := ‖v‖ + 1))
      AddSubgroup.isClosed_of_discreteTopology).image p).isDiscrete
    ⟨0, ⟨mem_closedBall_self (by positivity), L.zero_mem⟩, map_zero p⟩
  refine ⟨min ε 1, lt_min hε one_pos, ?_⟩
  intro y hy hpy
  by_contra! hlt
  obtain ⟨s, hs⟩ := hsplit y
  refine hpy (Set.mem_singleton_iff.mp (hball ▸ ⟨?_, y - (round s : ℝ) • v, ⟨?_, ?_⟩, ?_⟩))
  · exact mem_ball_zero_iff.mpr (hlt.trans_le (min_le_left _ _))
  · rw [mem_closedBall_zero_iff, ← sub_add_sub_cancel y (p y), hs, add_sub_left_comm, ← sub_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    nlinarith [norm_nonneg v, abs_sub_round s, hlt.trans_le (min_le_right ε 1)]
  · rw [Int.cast_smul_eq_zsmul]
    exact L.sub_mem hy (L.zsmul_mem hv _)
  · simp [hpv]

end

end ConvexGeometry

end ChangFreimanRuzsa
