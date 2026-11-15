/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Data.Pi.Interval
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Nat

/-!
# Generalized arithmetic progressions

A generalized arithmetic progression (GAP) in an additive monoid `G` is given by a dimension
`dim`, an `origin : G`, steps `step : Fin dim → G` and bounds `bound : Fin dim → ℕ`. Its points
are `origin + ∑ i, w i • step i` with `w ≤ bound`, and the length of the step `i` is
`bound i + 1`. A progression coerces to the finset of its points. The concatenation
`GAP.append P Q` adds the origins and concatenates the steps and the bounds, so that its points are
the sums of a point of `P` and a point of `Q`. The multiple `t • P` multiplies the origin and the
bound by `t`, so that its points are the sums of `t` points of `P`. The translate `c +ᵥ P` adds `c`
to the origin.

A progression `P` is `t`-proper when `t • P` is proper. For `t = 2` this says that the
concatenation of `P` with itself is proper, as in Bilu's condition `F₂` and in Tao and Vu. Green
and Tao call a progression with steps `s i` and lengths `ℓ i` `t`-proper when the points
`t • origin + ∑ i, w i • s i` with `w i < t * ℓ i` are distinct. The points of `t • P` are those
with `w i ≤ t * (ℓ i - 1)`, so the condition of Green and Tao is stronger. When every `bound i` is
positive, it follows from `(2 * t) • P` being proper, since `t * ℓ i - 1 ≤ 2 * t * (ℓ i - 1)` when
`2 ≤ ℓ i`. The progression `{0, 1}` in `ZMod 3` is `2`-proper but not `2`-proper in the sense of
Green and Tao.

## Main definitions

* `GAP G`: a generalized arithmetic progression in `G`, not necessarily proper.
* `GAP.eval`: the point with given coefficients.
* `GAP.toFinset`: the finset of points, which is the coercion `(P : Finset G)`.
* `GAP.Proper`: the points `origin + ∑ i, w i • step i` with `w ≤ bound` are distinct.
* `GAP.size`: the number `∏ i, (P.bound i + 1)` of coefficient vectors.
* `GAP.append`: the concatenation of two progressions.
* `stepsHom` and `stepHom`: the homomorphism from `ℤ ^ d` to `G` given by the steps.

## Main statements

* `GAP.toFinset_append`: the points of `GAP.append P Q` are the sums of a point of `P` and a point
  of `Q`.
* `GAP.toFinset_vadd`: the points of `c +ᵥ P` are the translates by `c` of the points of `P`.
* `GAP.proper_iff_card_eq_size`: a GAP `P` is proper if and only if it has `P.size` elements.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open scoped Finset Pointwise

noncomputable section

/-- A generalized arithmetic progression, not necessarily proper: the set of the points
`origin + ∑ i, w i • step i` with `w ≤ bound`. -/
structure GAP (G : Type*) [AddCommMonoid G] where
  /-- The number of steps. -/
  dim : ℕ
  /-- The base point. -/
  origin : G
  /-- The steps. -/
  step : Fin dim → G
  /-- The largest coefficient of each step. The length of the step `i` is `bound i + 1`. -/
  bound : Fin dim → ℕ

namespace GAP

variable {G : Type*} [AddCommMonoid G]

/-- The point `origin + ∑ i, w i • step i`. -/
def eval (P : GAP G) (w : Fin P.dim → ℕ) : G := P.origin + ∑ i, w i • P.step i

/-- The set of points of a progression. -/
@[coe] def toFinset [DecidableEq G] (P : GAP G) : Finset G := (Finset.Iic P.bound).image P.eval

instance [DecidableEq G] : CoeOut (GAP G) (Finset G) := ⟨toFinset⟩

/-- A progression is proper if the points `origin + ∑ i, w i • step i` with `w ≤ bound` are
distinct. -/
def Proper (P : GAP G) : Prop := Set.InjOn P.eval (Set.Iic P.bound)

/-- The number `∏ i, (P.bound i + 1)` of coefficient vectors `w ≤ P.bound` of a GAP. -/
def size (P : GAP G) : ℕ := ∏ i, (P.bound i + 1)

/-- The multiple `t • P` of a progression multiplies the origin and the bound by `t`. A progression
`P` is `t`-proper when `t • P` is proper. -/
instance : SMul ℕ (GAP G) where
  smul t P := ⟨P.dim, t • P.origin, P.step, t • P.bound⟩

/-- The concatenation of two progressions adds the origins and concatenates the steps and the
bounds. -/
def append (P Q : GAP G) : GAP G :=
  ⟨P.dim + Q.dim, P.origin + Q.origin, Fin.append P.step Q.step, Fin.append P.bound Q.bound⟩

/-- The translate `c +ᵥ P` of a progression adds `c` to the origin. -/
instance : VAdd G (GAP G) where
  vadd c P := ⟨P.dim, c + P.origin, P.step, P.bound⟩

/-! ## Points -/

@[simp] lemma dim_nsmul (t : ℕ) (P : GAP G) : (t • P).dim = P.dim := rfl

@[simp] lemma eval_zero (P : GAP G) : P.eval 0 = P.origin := by
  simp [eval]

section Carrier

variable [DecidableEq G]

lemma mem_toFinset {P : GAP G} {x : G} : x ∈ (P : Finset G) ↔ ∃ w ≤ P.bound, P.eval w = x := by
  simp [toFinset]

lemma eval_mem_toFinset (P : GAP G) {w : Fin P.dim → ℕ} (hw : w ≤ P.bound) :
    P.eval w ∈ (P : Finset G) :=
  mem_toFinset.2 ⟨w, hw, rfl⟩

lemma origin_mem (P : GAP G) : P.origin ∈ (P : Finset G) := by
  simpa using P.eval_mem_toFinset (w := 0) zero_le

lemma nonempty (P : GAP G) : (P : Finset G).Nonempty :=
  ⟨_, P.origin_mem⟩

end Carrier

/-! ## The size of a progression -/

lemma size_eq_card_Iic (P : GAP G) : P.size = (Finset.Iic P.bound).card := by
  simp [size, Pi.card_Iic]

section Size

variable [DecidableEq G]

lemma card_le_size (P : GAP G) : #(P : Finset G) ≤ P.size :=
  Finset.card_image_le.trans_eq P.size_eq_card_Iic.symm

/-- A GAP `P` is proper if and only if it has `P.size` elements. This is the definition of
properness of Chang and of Green. -/
lemma proper_iff_card_eq_size (P : GAP G) : P.Proper ↔ #(P : Finset G) = P.size := by
  rw [size_eq_card_Iic, toFinset, Finset.card_image_iff, Finset.coe_Iic]
  rfl

lemma card_eq_size {P : GAP G} (h : P.Proper) : #(P : Finset G) = P.size :=
  P.proper_iff_card_eq_size.1 h

end Size

/-! ## Concatenation -/

@[simp] lemma dim_append (P Q : GAP G) : (append P Q).dim = P.dim + Q.dim := rfl

/-- The point of `GAP.append P Q` with coefficients `Fin.append u v` is the sum of the points of `P`
and of `Q` with coefficients `u` and `v`. -/
private lemma eval_append (P Q : GAP G) (u : Fin P.dim → ℕ) (v : Fin Q.dim → ℕ) :
    (append P Q).eval (Fin.append u v) = P.eval u + Q.eval v := by
  unfold append
  simp only [eval, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  exact add_add_add_comm _ _ _ _

/-- A function `w ≤ Fin.append a b` is the concatenation of functions below `a` and `b`. -/
private lemma le_append_iff {m n : ℕ} {a : Fin m → ℕ} {b : Fin n → ℕ} {w : Fin (m + n) → ℕ} :
    w ≤ Fin.append a b ↔ (fun i ↦ w (Fin.castAdd n i)) ≤ a ∧ (fun i ↦ w (Fin.natAdd m i)) ≤ b := by
  simp [Pi.le_def, Fin.forall_fin_add]

/-- The points of `GAP.append P Q` are the sums of a point of `P` and a point of `Q`. -/
@[simp, norm_cast]
lemma toFinset_append [DecidableEq G] (P Q : GAP G) :
    (append P Q : Finset G) = P + Q := by
  ext x
  simp only [mem_toFinset, Finset.mem_add]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨u, v, rfl⟩ : ∃ u v, Fin.append u v = w := ⟨_, _, Fin.append_castAdd_natAdd⟩
    obtain ⟨hu, hv⟩ := le_append_iff.1 hw
    exact ⟨_, ⟨u, by simpa using hu, rfl⟩, _, ⟨v, by simpa using hv, rfl⟩, (eval_append ..).symm⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨Fin.append u v, le_append_iff.2 (by simpa using ⟨hu, hv⟩), eval_append ..⟩

lemma size_append (P Q : GAP G) : (append P Q).size = P.size * Q.size := by
  unfold append
  simp [size, Fin.prod_univ_add]

/-! ## Translates -/

@[simp] lemma dim_vadd (c : G) (P : GAP G) : (c +ᵥ P).dim = P.dim := rfl

/-- The points of `c +ᵥ P` are the translates by `c` of the points of `P`. -/
@[simp, norm_cast]
lemma toFinset_vadd [DecidableEq G] (c : G) (P : GAP G) :
    (c +ᵥ P : Finset G) = c +ᵥ (P : Finset G) := by
  rw [Finset.vadd_finset_def, toFinset, toFinset, Finset.image_image]
  congr 1
  funext w
  exact add_assoc _ _ _

end GAP

/-! ## The step homomorphism

It is defined for a GAP in an abelian group, where coefficients may be taken in `ℤ`.
-/

section Steps

variable {G : Type*} [AddCommGroup G]

/-- The homomorphism `(Fin d → ℤ) →+ G` attached to a family of steps: the integer linear
combination `Fintype.linearCombination ℤ step`. -/
def stepsHom {d : ℕ} (step : Fin d → G) : (Fin d → ℤ) →+ G :=
  (Fintype.linearCombination ℤ step).toAddMonoidHom

lemma stepsHom_apply {d : ℕ} (step : Fin d → G) (v : Fin d → ℤ) :
    stepsHom step v = ∑ i, v i • step i :=
  Fintype.linearCombination_apply ℤ step v

/-- On nonnegative coefficients the step homomorphism agrees with the `ℕ`-linear combination. -/
lemma stepsHom_natCast {d : ℕ} (step : Fin d → G) (w : (i : Fin d) → ℕ) :
    stepsHom step (fun i ↦ (w i : ℤ)) = ∑ i, w i • step i := by
  simp [stepsHom_apply]

end Steps

variable {G : Type*} [AddCommGroup G]

/-- The homomorphism `(Fin P.dim → ℤ) →+ G` given by the steps of a GAP. -/
def stepHom (P : GAP G) : (Fin P.dim → ℤ) →+ G := stepsHom P.step

/-- The point of a GAP with prescribed coefficients, read through the step homomorphism. -/
lemma GAP.eval_eq_stepsHom (P : GAP G) (w : Fin P.dim → ℕ) :
    P.eval w = P.origin + stepsHom P.step fun i ↦ (w i : ℤ) := by
  rw [stepsHom_natCast]
  rfl

end

end ChangFreimanRuzsa
