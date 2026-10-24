/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Pi.Interval
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Data.Rat.Floor

/-!
# Geometry of numbers for the relation lattice of a progression

This file contains the geometry of numbers used to make generalized arithmetic progressions proper.
The ambient lattice is `ℤ ^ d`, the convex body is a box, and the sublattice is the lattice of
relations among the steps of a progression.

## Main definitions and statements

- `intBox` and `natBox`: the symmetric and the nonnegative integer boxes, as intervals of `ℤ ^ d`
  for the pointwise order, with their cardinalities.
- `card_mul_prod_le_of_separated`: the packing bound. A set of points of a box that are pairwise
  far apart is small.
- `IsShort` and `HasIndependentShort`: a dilate of a box contains a vector, or a given number of
  linearly independent vectors, of a subgroup.

`ChangFreimanRuzsa.Properization.ShortRelationsAndIteration` applies these to the coefficient box
of a progression. `ChangFreimanRuzsa.BohrProgression` uses only `IsShort`, and takes its short
lattice vectors from Minkowski's second theorem in `ChangFreimanRuzsa.MinkowskiSecond`.
-/

@[expose] public section

namespace ChangFreimanRuzsa

noncomputable section

/-! ## Integer boxes -/

section Box

variable {d : ℕ}

/-- The symmetric box of the integer vectors `v` with `|v i| ≤ m i` for every `i`. -/
def intBox (m : Fin d → ℕ) : Finset (Fin d → ℤ) :=
  Finset.Icc (fun i ↦ -(m i : ℤ)) fun i ↦ (m i : ℤ)

/-- The nonnegative box of the integer vectors `v` with `0 ≤ v i ≤ m i` for every `i`. -/
def natBox (m : Fin d → ℕ) : Finset (Fin d → ℤ) :=
  Finset.Icc 0 fun i ↦ (m i : ℤ)

lemma mem_intBox {m : Fin d → ℕ} {v : Fin d → ℤ} : v ∈ intBox m ↔ ∀ i, |v i| ≤ m i := by
  simp [intBox, Pi.le_def, abs_le, ← forall_and]

lemma mem_natBox {m : Fin d → ℕ} {v : Fin d → ℤ} : v ∈ natBox m ↔ ∀ i, 0 ≤ v i ∧ v i ≤ m i := by
  simp [natBox, Pi.le_def, ← forall_and]

@[simp] lemma zero_mem_intBox (m : Fin d → ℕ) : (0 : Fin d → ℤ) ∈ intBox m :=
  mem_intBox.mpr fun i ↦ by simp

lemma card_intBox (m : Fin d → ℕ) : (intBox m).card = ∏ i, (2 * m i + 1) := by
  rw [intBox, Pi.card_Icc]
  congr with i
  rw [Int.card_Icc]
  grind

lemma card_natBox (m : Fin d → ℕ) : (natBox m).card = ∏ i, (m i + 1) := by
  rw [natBox, Pi.card_Icc]
  congr with i
  simp

/-- The difference of two points of the nonnegative box of half-widths `m` lies in the symmetric
box of half-widths `m`. -/
lemma sub_mem_intBox {m : Fin d → ℕ} {v w : Fin d → ℤ} (hv : v ∈ natBox m) (hw : w ∈ natBox m) :
    v - w ∈ intBox m := by
  rw [mem_natBox] at hv hw
  rw [mem_intBox]
  intro i
  simp only [Pi.sub_apply, abs_le]
  grind [hv i, hw i]

/-- The sum of a point of the symmetric box of half-widths `m` and a point of the nonnegative box of
half-widths `m'` lies in the symmetric box of half-widths `m + m'`. -/
lemma add_mem_intBox {m m' : Fin d → ℕ} {v w : Fin d → ℤ} (hv : v ∈ intBox m)
    (hw : w ∈ natBox m') : v + w ∈ intBox fun i ↦ m i + m' i := by
  rw [mem_intBox] at hv ⊢
  rw [mem_natBox] at hw
  intro i
  simp only [Pi.add_apply, abs_le, Nat.cast_add]
  grind [abs_le.mp (hv i), hw i]

end Box

/-! ## The packing bound

A set `s` of integer points that are pairwise far apart in the box metric is sparse: the
translates of the nonnegative box of half-widths `m` by the points of `s` are disjoint, hence fit
in an enlarged box. This is the counting form of the volume packing argument. -/

section Packing

variable {d : ℕ}

/-- If any two distinct points of `s` differ by more than `m i` in some coordinate `i`, then the
translates of the nonnegative box of half-widths `m` by the points of `s` are disjoint. -/
lemma injOn_add_of_separated {s : Finset (Fin d → ℤ)} {m : Fin d → ℕ}
    (hsep : ∀ u ∈ s, ∀ w ∈ s, u ≠ w → ∃ i, m i < |u i - w i|) :
    Set.InjOn (fun ((u, a) : (Fin d → ℤ) × (Fin d → ℤ)) ↦ u + a) ↑(s ×ˢ natBox m) := by
  rintro ⟨u, a⟩ hp ⟨u', a'⟩ hp' hsum
  obtain ⟨hu, ha⟩ := Finset.mem_product.mp hp
  obtain ⟨hu', ha'⟩ := Finset.mem_product.mp hp'
  obtain rfl : u = u' := by
    by_contra hne
    obtain ⟨i, hi⟩ := hsep u hu u' hu' hne
    grind [lt_abs, abs_le, mem_intBox.mp (sub_mem_intBox ha ha') i, congr_fun hsum i,
      Pi.add_apply, Pi.sub_apply]
  simpa using hsum

/-- The packing bound: if `s` lies in the symmetric box of half-widths `M` and any two distinct
points of `s` differ by more than `m i` in some coordinate `i`, then
`#s * ∏ i, (m i + 1) ≤ ∏ i, (2 * (M i + m i) + 1)`. -/
lemma card_mul_prod_le_of_separated {s : Finset (Fin d → ℤ)} {m M : Fin d → ℕ}
    (hbox : s ⊆ intBox M) (hsep : ∀ u ∈ s, ∀ w ∈ s, u ≠ w → ∃ i, m i < |u i - w i|) :
    s.card * ∏ i, (m i + 1) ≤ ∏ i, (2 * (M i + m i) + 1) := by
  rw [← card_natBox, ← Finset.card_product, ← card_intBox]
  refine Finset.card_le_card_of_injOn _ ?_ (injOn_add_of_separated hsep)
  rintro ⟨u, a⟩ hp
  obtain ⟨hu, ha⟩ := Finset.mem_product.mp hp
  exact add_mem_intBox (hbox hu) ha

end Packing

/-! ## Short independent vectors

`HasIndependentShort Λ L k t` says that the `t`-dilate of the box of half-widths `L` contains `k`
linearly independent vectors of a subgroup `Λ` of `ℤ ^ d`. Linear independence is taken over `ℤ`,
which for integer vectors is the same as linear independence over `ℝ`.

The properization does not use the successive minima of `Λ`. The relation lattice of a
progression in `ℤ` does not have full rank, so only the first few minima would be defined. The
largest `k` with `HasIndependentShort Λ L k t` for a fixed `t` is defined for every `Λ`, and it is
what `GAP.shortRelationRank` uses. -/

section ShortVectors

variable {d : ℕ}

/-- `IsShort L t v` says that `|v i| ≤ t * L i` for every `i`, that is, `v` lies in the `t`-dilate
of the box of half-widths `L`. -/
def IsShort (L : Fin d → ℕ) (t : ℝ) (v : Fin d → ℤ) : Prop := ∀ i, |(v i : ℝ)| ≤ t * L i

/-- `HasIndependentShort Λ L k t` says that the `t`-dilate of the box of half-widths `L` contains
`k` linearly independent vectors of `Λ`. -/
def HasIndependentShort (Λ : AddSubgroup (Fin d → ℤ)) (L : Fin d → ℕ) (k : ℕ) (t : ℝ) : Prop :=
  ∃ v : Fin k → (Fin d → ℤ), LinearIndependent ℤ v ∧ ∀ j, v j ∈ Λ ∧ IsShort L t (v j)

end ShortVectors

end

end ChangFreimanRuzsa
