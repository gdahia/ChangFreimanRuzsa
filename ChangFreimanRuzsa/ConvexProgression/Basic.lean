/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GAP.Basic
public import ChangFreimanRuzsa.GeometryOfNumbers.RealBox
import ChangFreimanRuzsa.GAP.Relations

/-!
# Convex progressions

A convex progression in an abelian group `G` is given by a dimension `dim`, an `origin : G`, a
homomorphism `hom : (Fin dim → ℤ) →+ G` and a body `body ⊆ ℝ ^ dim`. Its points are
`origin + hom v` with `v` an integer point of `body`. In Section 1 of Green's notes *Progressions
and convex geometry* the body is a full symmetric body, and the progression is `s`-proper when
`hom` is injective on the integer points of `s • body`.

A GAP `P` lies in the convex progression `P.toConvexProgression` with the same origin and steps and
the box `realBox (P.bound + 1)`. The box is wider than the coefficient box `0 ≤ w ≤ P.bound`, so
that it is a full symmetric body even when some `P.bound i` is `0`, and its volume is
`2 ^ P.dim * P.size`.

## Main definitions

* `ConvexProgression G`: a convex progression in `G`.
* `ConvexProgression.toSet`: the set of its points.
* `ConvexProgression.TProper s`: `hom` is injective on the integer points of `s • body`.
* `GAP.toConvexProgression`: the convex progression of the box of a GAP.

## Main statements

* `GAP.coe_toFinset_subset_toSet`: a GAP lies in its convex progression.
* `GAP.isFullSymmetricBody_toConvexProgression` and `GAP.volume_real_body_toConvexProgression`:
  the box is a full symmetric body of volume `2 ^ P.dim * P.size`.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open MeasureTheory Set
open scoped Pointwise

noncomputable section

/-- A convex progression: the set of the points `origin + hom v` with `v` an integer point of
`body`. -/
structure ConvexProgression (G : Type*) [AddCommGroup G] where
  /-- The dimension of the ambient lattice. -/
  dim : ℕ
  /-- The base point. -/
  origin : G
  /-- The homomorphism from the lattice to `G`. -/
  hom : (Fin dim → ℤ) →+ G
  /-- The body whose integer points parametrize the progression. -/
  body : Set (Fin dim → ℝ)

namespace ConvexProgression

variable {G : Type*} [AddCommGroup G] {P : ConvexProgression G}

/-- The set of points `origin + hom v` with `v` an integer point of `body`. -/
def toSet (P : ConvexProgression G) : Set G := P.origin +ᵥ P.hom '' latticePoints P.body

lemma mem_toSet {x : G} : x ∈ P.toSet ↔ ∃ v ∈ latticePoints P.body, P.origin + P.hom v = x := by
  simp [toSet, mem_vadd_set]

/-- A convex progression is `s`-proper if `hom` is injective on the integer points of
`s • body`. -/
def TProper (s : ℝ) (P : ConvexProgression G) : Prop := InjOn P.hom (latticePoints (s • P.body))

lemma TProper.mono (hP : IsFullSymmetricBody P.body) {a b : ℝ} (hab : |a| ≤ |b|)
    (h : P.TProper b) : P.TProper a :=
  InjOn.mono (latticePoints_mono (hP.smul_subset_smul hab)) h

end ConvexProgression

namespace GAP

variable {G : Type*} [AddCommGroup G]

/-- The convex progression with the origin and the steps of `P` and the box of half-widths
`P.bound i + 1`. -/
abbrev toConvexProgression (P : GAP G) : ConvexProgression G :=
  ⟨P.dim, P.origin, stepsHom P.step, realBox (P.bound + 1)⟩

/-- A GAP lies in its convex progression. -/
lemma coe_toFinset_subset_toSet [DecidableEq G] (P : GAP G) :
    (P : Set G) ⊆ P.toConvexProgression.toSet := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := (P.mem_toFinset_iff_exists_intCoeffs).1 hx
  refine ConvexProgression.mem_toSet.2 ⟨c, mem_realBox.2 ?_, rfl⟩
  intro i
  rw [intVectorToReal_apply]
  have h : |c i| ≤ ((P.bound i + 1 : ℕ) : ℤ) := by grind [abs_le]
  exact_mod_cast h

lemma isFullSymmetricBody_toConvexProgression (P : GAP G) :
    IsFullSymmetricBody P.toConvexProgression.body :=
  isFullSymmetricBody_realBox fun _ ↦ Nat.succ_pos _

lemma volume_real_body_toConvexProgression (P : GAP G) :
    volume.real P.toConvexProgression.body = 2 ^ P.dim * P.size := by
  rw [toConvexProgression, volume_real_realBox, size, Nat.cast_prod, ← Fin.prod_const,
    ← Finset.prod_mul_distrib]
  rfl

end GAP

end

end ChangFreimanRuzsa
