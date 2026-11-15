/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Chang's theorem

Chang's polynomial form of Freiman's theorem for finite sets of integers and for subsets of
`ZMod q` with `q` prime: for every `2 ≤ t`, a set with small doubling lies in a `t`-proper
generalized arithmetic progression of comparable size. Also the Bogolyubov–Ruzsa lemma, the first
step of its proof: for such a set `X`, the set `2 • X - 2 • X` contains a large proper generalized
arithmetic progression.

A convex progression in an abelian group `G` has a dimension `dim`, an `origin : G`, a
homomorphism `hom : (Fin dim → ℤ) →+ G` and a convex body `body` in `Fin dim → ℝ`, and its points
are `origin + hom v` with `v` a lattice point of `body`. It is `t`-proper when `hom` is injective on
the lattice points of `t • body`. A generalized arithmetic progression is the convex progression
with steps `step i` and bounds `bound i` for `i : Fin dim`, whose homomorphism is
`v ↦ ∑ i, v i • step i` and whose body is the box `0 ≤ x ≤ bound`. Its points are
`origin + ∑ i, w i • step i` with `w ≤ bound`, and it is `t`-proper when the points of its
multiple with origin `t • origin` and bound `t • bound` are distinct.

The proofs are in `Solution.lean`.
-/

@[expose] public section

open Finset
open scoped Pointwise

namespace ConvexBody

variable {d : ℕ} {𝒦 : ConvexBody (Fin d → ℝ)} {ℓ : Fin d → ℤ}

/-- A convex body in `Fin d → ℝ` has finitely many lattice points, because it is compact. -/
lemma finite_setOf_intCast_mem (𝒦 : ConvexBody (Fin d → ℝ)) :
    {ℓ : Fin d → ℤ | (fun i ↦ (ℓ i : ℝ)) ∈ 𝒦}.Finite :=
  ((Topology.IsClosedEmbedding.piMap fun _ ↦ Int.isClosedEmbedding_coe_real).isCompact_preimage
    𝒦.isCompact).finite_of_discrete

/-- The lattice points of a convex body `𝒦` in `Fin d → ℝ` are the `ℓ : Fin d → ℤ` that lie in `𝒦`.
They form a finset because `𝒦` is compact. -/
noncomputable def latticePoints (𝒦 : ConvexBody (Fin d → ℝ)) : Finset (Fin d → ℤ) :=
  𝒦.finite_setOf_intCast_mem.toFinset

/-- The box with dimensions `L` is the convex body of the `x : Fin d → ℝ` with `0 ≤ x` and
`x i ≤ L i` for all `i`. -/
def box (L : Fin d → ℕ) : ConvexBody (Fin d → ℝ) where
  carrier := Set.Icc 0 fun i ↦ (L i : ℝ)
  convex' := convex_Icc ..
  isCompact' := isCompact_Icc
  nonempty' := Set.nonempty_Icc.2 fun _ ↦ by simp

end ConvexBody

/-- A convex progression: the set of the points `origin + hom v` with `v` a lattice point of
`body`. -/
structure ConvexProgression (G : Type*) [AddCommGroup G] where
  /-- The dimension of the ambient lattice. -/
  dim : ℕ
  /-- The base point. -/
  origin : G
  /-- The homomorphism from the lattice to `G`. -/
  hom : (Fin dim → ℤ) →+ G
  /-- The convex body whose lattice points parametrize the progression. -/
  body : ConvexBody (Fin dim → ℝ)

namespace ConvexProgression

variable {G : Type*} [AddCommGroup G] {P : ConvexProgression G}

/-- The finset of points of a convex progression. -/
noncomputable def toFinset [DecidableEq G] (P : ConvexProgression G) : Finset G :=
  P.body.latticePoints.image fun v ↦ P.origin + P.hom v

/-- A convex progression is `t`-proper if `hom` is injective on the lattice points of
`t • body`. -/
def Proper (t : ℝ) (P : ConvexProgression G) : Prop := Set.InjOn P.hom (t • P.body).latticePoints

end ConvexProgression

namespace GAP

variable {G : Type*} [AddCommGroup G]

/-- The homomorphism `(Fin d → ℤ) →+ G` given by steps `step : Fin d → G`: the integer linear
combination `Fintype.linearCombination ℤ step`. -/
def stepsHom {d : ℕ} (step : Fin d → G) : (Fin d → ℤ) →+ G :=
  (Fintype.linearCombination ℤ step).toAddMonoidHom

end GAP

/-- A generalized arithmetic progression: the convex progression with homomorphism
`GAP.stepsHom step` and body `ConvexBody.box bound`, whose points are the
`origin + ∑ i, w i • step i` with `w ≤ bound`. -/
structure GAP (G : Type*) [AddCommGroup G] extends ConvexProgression G where
  /-- The steps. -/
  step : Fin dim → G
  /-- The largest coefficient of each step. The length of the step `i` is `bound i + 1`. -/
  bound : Fin dim → ℕ
  hom := GAP.stepsHom step
  body := .box bound
  /-- The homomorphism of the convex progression is given by the steps. -/
  hom_eq : hom = GAP.stepsHom step := by rfl
  /-- The body of the convex progression is the box of the bounds. -/
  body_eq : body = .box bound := by rfl

namespace ChangFreimanRuzsa

/-- **Bogolyubov–Ruzsa lemma** for sets of integers, with the bounds of Chang. If a finite nonempty
set `X` of integers satisfies `#(X + X) ≤ κ * #X`, where `2 ≤ κ`, then `2 • X - 2 • X` contains a
proper generalized arithmetic progression `Q` of dimension at most
`3 * 10 ^ 5 * κ * (1 + Real.log κ)` with
`#X ≤ Real.exp (2 * 10 ^ 7 * κ * (1 + Real.log κ) ^ 2) * #Q.toFinset`. -/
theorem exists_proper_gap_subset_nsmul_sub_nsmul_dim_le_card_le' {κ : ℝ} (X : Finset ℤ)
    (hX : X.Nonempty) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X) :
    ∃ Q : GAP ℤ, Q.Proper 1 ∧ Q.toFinset ⊆ 2 • X - 2 • X ∧
      Q.dim ≤ 3 * 10 ^ 5 * κ * (1 + Real.log κ) ∧
      #X ≤ Real.exp (2 * 10 ^ 7 * κ * (1 + Real.log κ) ^ 2) * #Q.toFinset :=
  sorry

/-- **Bogolyubov–Ruzsa lemma** in `ZMod q` for a prime `q`, with the bounds of Chang. If a nonempty
set `X` satisfies `#(X + X) ≤ κ * #X`, where `2 ≤ κ`, then `2 • X - 2 • X` contains a proper
generalized arithmetic progression `Q` of dimension at most `3 * 10 ^ 5 * κ * (1 + Real.log κ)`
with `#X ≤ Real.exp (2 * 10 ^ 7 * κ * (1 + Real.log κ) ^ 2) * #Q.toFinset`. -/
theorem exists_proper_gap_zmod_subset_nsmul_sub_nsmul_dim_le_card_le' {q : ℕ} {κ : ℝ}
    (X : Finset (ZMod q)) (hq : q.Prime) (hX : X.Nonempty) (hκ : 2 ≤ κ)
    (hXX : #(X + X) ≤ κ * #X) :
    ∃ Q : GAP (ZMod q), Q.Proper 1 ∧ Q.toFinset ⊆ 2 • X - 2 • X ∧
      Q.dim ≤ 3 * 10 ^ 5 * κ * (1 + Real.log κ) ∧
      #X ≤ Real.exp (2 * 10 ^ 7 * κ * (1 + Real.log κ) ^ 2) * #Q.toFinset :=
  sorry

/-- **Chang's theorem** for sets of integers. Let `2 ≤ t`. A finite nonempty set `X` of integers
with `#(X + X) ≤ κ * #X`, where `2 ≤ κ`, is contained in a `t`-proper generalized arithmetic
progression of dimension at most `2 * κ - 1` with at most
`Real.exp (2 * 10 ^ 11 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X` points. -/
theorem exists_tProperGAP_subset_dim_le_card_le' {t : ℕ} {κ : ℝ} (X : Finset ℤ) (hX : X.Nonempty)
    (ht : 2 ≤ t) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X) :
    ∃ P : GAP ℤ, P.Proper t ∧ X ⊆ P.toFinset ∧ P.dim ≤ 2 * κ - 1 ∧
      #P.toFinset ≤
        Real.exp (2 * 10 ^ 11 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X :=
  sorry

/-- **Chang's theorem** in `ZMod q` for a prime `q`. Let `2 ≤ t`. A set `X` with
`#(X + X) ≤ κ * #X`, where `2 ≤ κ`, with at least `7 * 10 ^ 7 * κ ^ 2` elements and with
`Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X ≤ q`, is contained in a
`t`-proper generalized arithmetic progression of dimension at most `2 * κ - 1` with at most
`Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X` points. -/
theorem exists_tProperGAP_zmod_subset_dim_le_card_le' {q t : ℕ} {κ : ℝ} (X : Finset (ZMod q))
    (hq : q.Prime) (ht : 2 ≤ t) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X)
    (hXlower : 7 * 10 ^ 7 * κ ^ 2 ≤ #X)
    (hXupper : Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X ≤ q) :
    ∃ Q : GAP (ZMod q), Q.Proper t ∧ X ⊆ Q.toFinset ∧ Q.dim ≤ 2 * κ - 1 ∧
      #Q.toFinset ≤
        Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X :=
  sorry

/-- **Chang's theorem** for sets of integers, with the dimension bound of Green and Tao. Let
`2 ≤ t`. A finite set `X` of integers with `#(X + X) ≤ κ * #X`, where `2 ≤ κ`, and with
`κ * (2 * κ - 1) ≤ ε * #X` is contained in a `t`-proper generalized arithmetic progression of
dimension at most `⌊κ - 1 + ε⌋₊` with at most
`Real.exp (2 * 10 ^ 11 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X` points. -/
theorem exists_tProperGAP_subset_dim_le_floor_card_le' {t : ℕ} {κ ε : ℝ} (X : Finset ℤ) (ht : 2 ≤ t)
    (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X) (hXε : κ * (2 * κ - 1) ≤ ε * #X) :
    ∃ P : GAP ℤ, P.Proper t ∧ X ⊆ P.toFinset ∧ P.dim ≤ ⌊κ - 1 + ε⌋₊ ∧
      #P.toFinset ≤
        Real.exp (2 * 10 ^ 11 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X :=
  sorry

/-- **Chang's theorem** in `ZMod q` for a prime `q`, with the dimension bound of Green and Tao. Let
`2 ≤ t`. A set `X` with `#(X + X) ≤ κ * #X`, where `2 ≤ κ`, with at least `7 * 10 ^ 7 * κ ^ 2`
elements, with `Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X ≤ q`
and with `κ * (2 * κ - 1) ≤ ε * #X` is contained in a `t`-proper generalized arithmetic progression
of dimension at most `⌊κ - 1 + ε⌋₊` with at most
`Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X` points. -/
theorem exists_tProperGAP_zmod_subset_dim_le_floor_card_le' {q t : ℕ} {κ ε : ℝ}
    (X : Finset (ZMod q)) (hq : q.Prime) (ht : 2 ≤ t) (hκ : 2 ≤ κ) (hXX : #(X + X) ≤ κ * #X)
    (hXlower : 7 * 10 ^ 7 * κ ^ 2 ≤ #X)
    (hXupper : Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X ≤ q)
    (hXε : κ * (2 * κ - 1) ≤ ε * #X) :
    ∃ Q : GAP (ZMod q), Q.Proper t ∧ X ⊆ Q.toFinset ∧ Q.dim ≤ ⌊κ - 1 + ε⌋₊ ∧
      #Q.toFinset ≤
        Real.exp (10 ^ 10 * κ ^ 2 * (1 + Real.log κ) ^ 3 + 2 * κ * Real.log t) * #X :=
  sorry

end ChangFreimanRuzsa
