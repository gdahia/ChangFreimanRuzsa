/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.IntVectorToReal
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Bornology.Constructions
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import ChangFreimanRuzsa.Lattice

/-! # The real box of a box of integer points

The lattice box step of properization uses the shortest lattice vectors of
`ChangFreimanRuzsa.ConvexGeometry`, which are defined for a discrete subgroup of a real normed space
and a symmetric convex body. This file passes from a subgroup $\Lambda$ of $\mathbb{Z}^d$ and the
box of half-widths $L$ to these objects, along the coordinatewise inclusion
`intVectorToReal` of $\mathbb{Z}^d$ into $\mathbb{R}^d$.

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

/-! ## The real box is a symmetric convex body -/

/-- The real box $\{x \in \mathbb{R}^d : |x_i| \le L_i \text{ for all } i\}$ of half-widths
$L$. -/
def realBox (L : Fin d → ℕ) : Set (Fin d → ℝ) :=
  Set.univ.pi fun i ↦ Set.Icc (-(L i : ℝ)) (L i)

lemma mem_realBox {L : Fin d → ℕ} {x : Fin d → ℝ} :
    x ∈ realBox L ↔ ∀ i, |x i| ≤ L i := by
  simp [realBox, abs_le, Pi.le_def, forall_and]

lemma convex_realBox (L : Fin d → ℕ) : Convex ℝ (realBox L) :=
  convex_pi fun _ _ ↦ convex_Icc _ _

lemma neg_mem_realBox {L : Fin d → ℕ} {x : Fin d → ℝ} (hx : x ∈ realBox L) :
    -x ∈ realBox L := by
  simpa [mem_realBox] using hx

lemma isClosed_realBox (L : Fin d → ℕ) : IsClosed (realBox L) :=
  isClosed_set_pi fun _ _ ↦ isClosed_Icc

lemma isBounded_realBox (L : Fin d → ℕ) : Bornology.IsBounded (realBox L) :=
  Bornology.IsBounded.pi fun _ ↦ Metric.isBounded_Icc _ _

lemma isCompact_realBox (L : Fin d → ℕ) : IsCompact (realBox L) :=
  isCompact_univ_pi fun _ ↦ isCompact_Icc

lemma realBox_mem_nhds {L : Fin d → ℕ} (hL : ∀ i, 0 < L i) :
    realBox L ∈ 𝓝 (0 : Fin d → ℝ) := by
  apply set_pi_mem_nhds Set.finite_univ
  intro i _
  apply Icc_mem_nhds <;> simpa using hL i

/-! ## The image of a subgroup of `ℤ ^ d` is discrete -/

/-- The image in $\mathbb{R}^d$ of a subgroup of $\mathbb{Z}^d$ is discrete, because it lies in the
discrete subgroup `standardIntegerLattice d`. -/
lemma discreteTopology_map (Λ : AddSubgroup (Fin d → ℤ)) :
    DiscreteTopology (Λ.map intVectorToReal) := by
  refine DiscreteTopology.of_subset (standardIntegerLattice_discrete d) ?_
  rintro _ ⟨v, -, rfl⟩
  exact intVectorToReal_mem_standardIntegerLattice v

end

end BoxLattice

end ChangFreimanRuzsa
