/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.ConvexGeometry
public import ChangFreimanRuzsa.GeometryOfNumbers
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Lemmas

/-! # The real box of a box of integer points

The reboxing step of properization uses the successive minima of
`ChangFreimanRuzsa.ConvexGeometry`, which are defined for a discrete subgroup of a real normed space
and a symmetric convex body. This file passes from a subgroup $\Lambda$ of $\mathbb{Z}^d$ and the
box of half-widths $L$ to these objects, along the coordinatewise inclusion
`intCastHom` of $\mathbb{Z}^d$ into $\mathbb{R}^d$.

* `realBox L` is the set of $x \in \mathbb{R}^d$ with $|x_i| \le L_i$ for all $i$. The lemmas
  `convex_realBox`, `isClosed_realBox`, `isBounded_realBox`, `neg_mem_realBox` and
  `realBox_mem_nhds` show that it is a symmetric convex body.
* `discreteTopology_map` shows that the image of a subgroup of $\mathbb{Z}^d$ is a discrete
  subgroup of $\mathbb{R}^d$.
-/

@[expose] public section

namespace ChangFreimanRuzsa

namespace BoxLattice

open scoped Pointwise Topology

open Metric Module

noncomputable section

variable {d : ℕ}

/-! ## The inclusion of integer vectors -/

/-- The coordinatewise inclusion of integer vectors into real vectors. -/
def intCastHom : (Fin d → ℤ) →+ (Fin d → ℝ) where
  toFun v i := (v i : ℝ)
  map_zero' := by
    funext i
    simp
  map_add' u v := by
    funext i
    simp only [Pi.add_apply]
    push_cast
    ring

@[simp] lemma intCastHom_apply (v : Fin d → ℤ) (i : Fin d) : intCastHom v i = (v i : ℝ) := rfl

lemma intCastHom_injective : Function.Injective (intCastHom : (Fin d → ℤ) → (Fin d → ℝ)) := by
  intro u v huv
  funext i
  simpa using congr_fun huv i

lemma intCastHom_zsmul (c : ℤ) (v : Fin d → ℤ) :
    intCastHom (c • v) = (c : ℝ) • intCastHom v := by
  rw [map_zsmul, Int.cast_smul_eq_zsmul]

/-! ## The real box is a symmetric convex body -/

/-- The real box $\{x \in \mathbb{R}^d : |x_i| \le L_i \text{ for all } i\}$ of half-widths
$L$. -/
def realBox (L : Fin d → ℕ) : Set (Fin d → ℝ) := {x | ∀ i, |x i| ≤ (L i : ℝ)}

lemma mem_realBox {L : Fin d → ℕ} {x : Fin d → ℝ} :
    x ∈ realBox L ↔ ∀ i, |x i| ≤ (L i : ℝ) := Iff.rfl

lemma convex_realBox (L : Fin d → ℕ) : Convex ℝ (realBox L) := by
  intro x hx y hy a b ha hb hab i
  rw [mem_realBox] at hx hy
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  apply le_trans (abs_add_le _ _)
  rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  nlinarith [hx i, hy i, abs_nonneg (x i), abs_nonneg (y i)]

lemma neg_mem_realBox (L : Fin d → ℕ) : ∀ x ∈ realBox L, -x ∈ realBox L := by
  intro x hx i
  simpa using hx i

lemma isClosed_realBox (L : Fin d → ℕ) : IsClosed (realBox L) := by
  rw [realBox, Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  exact isClosed_le (continuous_apply i).abs continuous_const

lemma isBounded_realBox (L : Fin d → ℕ) : Bornology.IsBounded (realBox L) := by
  apply Bornology.IsBounded.subset (Metric.isBounded_closedBall
    (x := (0 : Fin d → ℝ)) (r := ((Finset.univ.sup L : ℕ) : ℝ)))
  intro x hx
  rw [mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).mpr
  intro i
  rw [Real.norm_eq_abs]
  exact (hx i).trans (Nat.cast_le.mpr (Finset.le_sup (Finset.mem_univ i)))

lemma realBox_mem_nhds {L : Fin d → ℕ} (hL : ∀ i, 0 < L i) :
    realBox L ∈ 𝓝 (0 : Fin d → ℝ) := by
  apply Filter.mem_of_superset (Metric.ball_mem_nhds 0 zero_lt_one)
  intro x hx i
  rw [mem_ball_zero_iff] at hx
  linarith [norm_le_pi_norm x i, Real.norm_eq_abs (x i),
    (Nat.one_le_cast.2 (hL i) : (1 : ℝ) ≤ L i)]

/-! ## The image of a subgroup of `ℤ ^ d` is discrete -/

/-- The image in $\mathbb{R}^d$ of a subgroup of $\mathbb{Z}^d$ is discrete, because a nonzero
integer vector has sup norm at least $1$. -/
lemma discreteTopology_map (Λ : AddSubgroup (Fin d → ℤ)) :
    DiscreteTopology (Λ.map (intCastHom : (Fin d → ℤ) →+ (Fin d → ℝ))) := by
  refine ConvexGeometry.discreteTopology_of_exists_pos_forall_norm_lt ⟨1, one_pos, ?_⟩
  rintro x hx hnorm
  obtain ⟨v, hvΛ, rfl⟩ := AddSubgroup.mem_map.mp hx
  have hv : v = 0 := by
    funext i
    have hi := norm_le_pi_norm (intCastHom v) i
    rw [intCastHom_apply, Real.norm_eq_abs] at hi
    rw [Pi.zero_apply, ← Int.abs_lt_one_iff, ← Int.cast_lt (R := ℝ), Int.cast_abs, Int.cast_one]
    linarith
  rw [hv, map_zero]

end

end BoxLattice

end ChangFreimanRuzsa
