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

The reboxing step of properization works in a real normed space, with the successive minima of
`Chang.ConvexGeometry`. This file supplies the passage from a subgroup `Λ` of `ℤ ^ d` and the box
of half-widths `L`, along the coordinatewise inclusion `intCastHom : ℤ ^ d → ℝ ^ d`:

- `realBox` is the real box of half-widths `L`, and `convex_realBox`, `isClosed_realBox`,
  `isBounded_realBox`, `neg_mem_realBox` and `realBox_mem_nhds` say that it is a symmetric convex
  body;
- `discreteTopology_map` says that the image of a subgroup of `ℤ ^ d` is a discrete subgroup of
  `ℝ ^ d`, because a nonzero integer vector has sup norm at least one.
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
  have := congr_fun huv i
  rw [intCastHom_apply, intCastHom_apply] at this
  exact_mod_cast this

lemma intCastHom_zsmul (c : ℤ) (v : Fin d → ℤ) :
    intCastHom (c • v) = (c : ℝ) • intCastHom v := by
  rw [map_zsmul, Int.cast_smul_eq_zsmul]

/-! ## The real box is a symmetric convex body -/

/-- The real box of half-widths `L`. -/
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
  have hinter : realBox L = ⋂ i, {x : Fin d → ℝ | |x i| ≤ (L i : ℝ)} := by
    ext x
    simp only [mem_realBox, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [hinter]
  exact isClosed_iInter fun i ↦ isClosed_le ((continuous_apply i).abs) continuous_const

lemma isBounded_realBox (L : Fin d → ℕ) : Bornology.IsBounded (realBox L) := by
  apply Bornology.IsBounded.subset (Metric.isBounded_closedBall
    (x := (0 : Fin d → ℝ)) (r := ((Finset.univ.sup L : ℕ) : ℝ)))
  intro x hx
  rw [mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).mpr
  intro i
  refine le_trans (le_of_eq (Real.norm_eq_abs _)) (le_trans (hx i) (Nat.cast_le.mpr ?_))
  exact Finset.le_sup (Finset.mem_univ i)

lemma realBox_mem_nhds {L : Fin d → ℕ} (hL : ∀ i, 0 < L i) :
    realBox L ∈ 𝓝 (0 : Fin d → ℝ) := by
  apply Filter.mem_of_superset (Metric.ball_mem_nhds 0 zero_lt_one)
  intro x hx i
  rw [mem_ball_zero_iff] at hx
  have hxi : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
  have hLi : (1 : ℝ) ≤ (L i : ℝ) := by exact_mod_cast hL i
  rw [Real.norm_eq_abs] at hxi
  linarith

/-! ## The image of a subgroup of `ℤ ^ d` is discrete -/

/-- A nonzero integer vector has sup norm at least one, so the image of any subgroup of `ℤ ^ d`
avoids the unit ball around the origin. -/
lemma discreteTopology_map (Λ : AddSubgroup (Fin d → ℤ)) :
    DiscreteTopology (Λ.map (intCastHom : (Fin d → ℤ) →+ (Fin d → ℝ))) := by
  refine ConvexGeometry.discreteTopology_of_exists_pos_forall_norm_lt ⟨1, one_pos, ?_⟩
  rintro x hx hnorm
  obtain ⟨v, hvΛ, rfl⟩ := AddSubgroup.mem_map.mp hx
  have hv : v = 0 := by
    funext i
    have hi : ‖(intCastHom v : Fin d → ℝ) i‖ ≤ ‖(intCastHom v : Fin d → ℝ)‖ :=
      norm_le_pi_norm _ i
    rw [intCastHom_apply, Real.norm_eq_abs] at hi
    have hint : |v i| < 1 := by
      rw [← Int.cast_lt (R := ℝ), Int.cast_abs, Int.cast_one]
      linarith
    have := abs_lt.mp hint
    rw [Pi.zero_apply]
    omega
  rw [hv, map_zero]

end

end BoxLattice

end ChangFreimanRuzsa
