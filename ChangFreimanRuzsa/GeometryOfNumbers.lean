/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Pi.Interval
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-! # Geometry of numbers for the relation lattice of a progression

This file develops the geometry of numbers needed by the properization of generalized arithmetic
progressions, in the discrete form in which properization consumes it: the ambient lattice is
`ℤ ^ d`, the convex body is a box, and the sublattice is the lattice of relations among the steps
of a progression.

The main pieces are:

- `intBox` and `natBox`, the symmetric and the nonnegative integer boxes, with their cardinalities;
- `card_mul_prod_le_of_separated`, the **packing bound**: a set of points of a box that are
  pairwise far apart is small;
- `IsShort` and `HasIndependentShort`, which say that a dilate of a box contains a vector, or
  a given number of linearly independent vectors, of a subgroup.

`Chang.Properization` reads all of this through the coefficient box of a progression. The Bohr
stage, `Chang.BohrProgression`, takes its short lattice vectors from Minkowski's second theorem in
`Chang.MinkowskiSecond` instead, and uses only `IsShort` from this file.
-/

@[expose] public section

namespace ChangFreimanRuzsa

noncomputable section

/-! ## Integer boxes -/

section Box

variable {d : ℕ}

/-- The symmetric box of integer vectors with `|v i| ≤ m i`. -/
def intBox (m : Fin d → ℕ) : Finset (Fin d → ℤ) :=
  Finset.Icc (fun i ↦ -(m i : ℤ)) fun i ↦ (m i : ℤ)

/-- The nonnegative box of integer vectors with `0 ≤ v i ≤ m i`. -/
def natBox (m : Fin d → ℕ) : Finset (Fin d → ℤ) :=
  Finset.Icc 0 fun i ↦ (m i : ℤ)

lemma mem_intBox {m : Fin d → ℕ} {v : Fin d → ℤ} : v ∈ intBox m ↔ ∀ i, |v i| ≤ (m i : ℤ) := by
  simp only [intBox, Finset.mem_Icc, Pi.le_def, abs_le, ← forall_and]

lemma mem_natBox {m : Fin d → ℕ} {v : Fin d → ℤ} :
    v ∈ natBox m ↔ ∀ i, 0 ≤ v i ∧ v i ≤ (m i : ℤ) := by
  simp only [natBox, Finset.mem_Icc, Pi.le_def, Pi.zero_apply, ← forall_and]

@[simp] lemma zero_mem_intBox (m : Fin d → ℕ) : (0 : Fin d → ℤ) ∈ intBox m :=
  mem_intBox.mpr fun i ↦ by simp

lemma card_intBox (m : Fin d → ℕ) : (intBox m).card = ∏ i, (2 * m i + 1) := by
  rw [intBox, Pi.card_Icc]
  apply Finset.prod_congr rfl
  intro i _
  rw [Int.card_Icc]
  omega

lemma card_natBox (m : Fin d → ℕ) : (natBox m).card = ∏ i, (m i + 1) := by
  rw [natBox, Pi.card_Icc]
  apply Finset.prod_congr rfl
  intro i _
  rw [Int.card_Icc]
  simp

/-- A difference of two points of a box lies in the symmetric box of the same half-widths. -/
lemma sub_mem_intBox {m : Fin d → ℕ} {v w : Fin d → ℤ} (hv : v ∈ natBox m) (hw : w ∈ natBox m) :
    v - w ∈ intBox m := by
  rw [mem_natBox] at hv hw
  apply mem_intBox.mpr
  intro i
  have := hv i
  have := hw i
  simp only [Pi.sub_apply, abs_le]
  omega

/-- Translating a box by a point of a smaller box lands in the box of the added half-widths. -/
lemma add_mem_intBox {m m' : Fin d → ℕ} {v w : Fin d → ℤ} (hv : v ∈ intBox m)
    (hw : w ∈ natBox m') : v + w ∈ intBox fun i ↦ m i + m' i := by
  rw [mem_intBox] at hv
  rw [mem_natBox] at hw
  apply mem_intBox.mpr
  intro i
  have := abs_le.mp (hv i)
  have := hw i
  simp only [Pi.add_apply, abs_le, Nat.cast_add]
  omega

end Box

/-! ## The packing bound

A set of integer points that are pairwise far apart in the box metric is sparse: the translates of
a box of half-widths `m` by its elements are disjoint, hence fit in the enlarged box. This is the
counting form of the volume packing argument, and it is the one place where the geometry of numbers
gives an upper bound on the number of lattice points of a box. -/

section Packing

variable {d : ℕ}

/-- The packing bound: if distinct points of `s` are never within `m` of each other, and `s` lies
in the box of half-widths `M`, then `s` is small. -/
theorem card_mul_prod_le_of_separated {s : Finset (Fin d → ℤ)} {m M : Fin d → ℕ}
    (hbox : ∀ u ∈ s, ∀ i, |u i| ≤ (M i : ℤ))
    (hsep : ∀ u ∈ s, ∀ w ∈ s, u ≠ w → ∃ i, (m i : ℤ) < |u i - w i|) :
    s.card * ∏ i, (m i + 1) ≤ ∏ i, (2 * (M i + m i) + 1) := by
  classical
  rw [← card_natBox, ← Finset.card_product, ← card_intBox]
  apply Finset.card_le_card_of_injOn (fun p ↦ p.1 + p.2)
  · intro p hp
    rw [Finset.mem_coe, Finset.mem_product] at hp
    exact add_mem_intBox (mem_intBox.mpr (hbox p.1 hp.1)) hp.2
  · rintro ⟨u, a⟩ hp ⟨u', a'⟩ hp' hsum
    simp only [Finset.mem_coe, Finset.mem_product] at hp hp'
    simp only at hsum
    have hfst : u = u' := by
      by_contra hne
      obtain ⟨i, hi⟩ := hsep u hp.1 u' hp'.1 hne
      have hclose := abs_le.mp (mem_intBox.mp (sub_mem_intBox hp.2 hp'.2) i)
      have hcoord := congr_fun hsum i
      simp only [Pi.add_apply, Pi.sub_apply] at hclose hcoord
      rcases lt_abs.mp hi with h | h <;> omega
    rw [hfst] at hsum ⊢
    rw [add_left_cancel hsum]

end Packing

/-! ## Short independent vectors

`HasIndependentShort Λ L k t` says that the `t`-dilate of the box of half-widths `L` contains `k`
linearly independent vectors of a subgroup `Λ` of `ℤ ^ d`. Linear independence is taken over `ℤ`,
which for integer vectors is the same as linear independence over `ℝ`.

The properization does not use the successive minima of `Λ`. The relation lattice of a progression
in `ℤ` does not have full rank, so only the first few minima would be defined. The largest `k`
with `HasIndependentShort Λ L k t` for a fixed `t` is defined for every `Λ`, and it is what
`GAP.shortRelationRank` uses. -/

section ShortVectors

variable {d : ℕ}

/-- `IsShort L t v` says that `v` lies in the `t`-dilate of the box of half-widths `L`. -/
def IsShort (L : Fin d → ℕ) (t : ℝ) (v : Fin d → ℤ) : Prop := ∀ i, |(v i : ℝ)| ≤ t * L i

lemma IsShort.mono {L : Fin d → ℕ} {t t' : ℝ} {v : Fin d → ℤ} (h : IsShort L t v) (htt' : t ≤ t') :
    IsShort L t' v := fun i ↦
  (h i).trans (mul_le_mul_of_nonneg_right htt' (Nat.cast_nonneg _))

/-- `HasIndependentShort Λ L k t` says that the `t`-dilate of the box of half-widths `L` contains
`k` linearly independent vectors of `Λ`. -/
def HasIndependentShort (Λ : AddSubgroup (Fin d → ℤ)) (L : Fin d → ℕ) (k : ℕ) (t : ℝ) : Prop :=
  ∃ v : Fin k → (Fin d → ℤ), LinearIndependent ℤ v ∧ ∀ j, v j ∈ Λ ∧ IsShort L t (v j)

lemma HasIndependentShort.mono {Λ : AddSubgroup (Fin d → ℤ)} {L : Fin d → ℕ} {k : ℕ} {t t' : ℝ}
    (h : HasIndependentShort Λ L k t) (htt' : t ≤ t') : HasIndependentShort Λ L k t' := by
  obtain ⟨v, hindep, hv⟩ := h
  exact ⟨v, hindep, fun j ↦ ⟨(hv j).1, (hv j).2.mono htt'⟩⟩

lemma HasIndependentShort.of_le {Λ : AddSubgroup (Fin d → ℤ)} {L : Fin d → ℕ} {k k' : ℕ} {t : ℝ}
    (h : HasIndependentShort Λ L k t) (hk : k' ≤ k) : HasIndependentShort Λ L k' t := by
  obtain ⟨v, hindep, hv⟩ := h
  exact ⟨v ∘ Fin.castLE hk, hindep.comp _ (Fin.castLE_injective hk), fun j ↦ hv _⟩

end ShortVectors

end

end ChangFreimanRuzsa
