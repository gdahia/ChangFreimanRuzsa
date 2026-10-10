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
- `successiveMinimum`, the **successive minima** of a subgroup with respect to a box, together
  with `exists_witness_successiveMinimum` for the attainment of the infimum defining them.

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

/-! ## Successive minima

The `k`-th successive minimum of a subgroup `Λ` of `ℤ ^ d` with respect to the box of half-widths
`L` is the least dilation factor of the box whose points contain `k` linearly independent vectors
of `Λ`. Linear independence is taken over `ℤ`, which for integer vectors is the same as linear
independence over `ℝ`.

As in the literature the minima are defined as infima, and as in the literature the infimum is
attained, `exists_witness_successiveMinimum`. Both that and the positivity of the first minimum,
`le_successiveMinimum_one`, come from discreteness of `ℤ ^ d` rather than from compactness. -/

section SuccessiveMinima

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

/-- The `k`-th successive minimum of `Λ` with respect to the box of half-widths `L`. -/
def successiveMinimum (Λ : AddSubgroup (Fin d → ℤ)) (L : Fin d → ℕ) (k : ℕ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ HasIndependentShort Λ L k t}

lemma bddBelow_dilations (Λ : AddSubgroup (Fin d → ℤ)) (L : Fin d → ℕ) (k : ℕ) :
    BddBelow {t : ℝ | 0 ≤ t ∧ HasIndependentShort Λ L k t} :=
  ⟨0, fun _ ht ↦ ht.1⟩

/-- Any dilation factor realizing `k` independent vectors bounds the `k`-th minimum. -/
lemma successiveMinimum_le {Λ : AddSubgroup (Fin d → ℤ)} {L : Fin d → ℕ} {k : ℕ} {t : ℝ}
    (ht : 0 ≤ t) (h : HasIndependentShort Λ L k t) : successiveMinimum Λ L k ≤ t :=
  csInf_le (bddBelow_dilations Λ L k) ⟨ht, h⟩

/-- The successive minima increase with the number of independent vectors required. -/
lemma successiveMinimum_mono {Λ : AddSubgroup (Fin d → ℤ)} {L : Fin d → ℕ} {k k' : ℕ}
    (hk : k ≤ k') (hne : ∃ t, 0 ≤ t ∧ HasIndependentShort Λ L k' t) :
    successiveMinimum Λ L k ≤ successiveMinimum Λ L k' := by
  exact le_csInf hne fun t ht ↦ successiveMinimum_le ht.1 (ht.2.of_le hk)

/-- A dilation factor smaller than every minimum bounds it from below. -/
lemma le_successiveMinimum {Λ : AddSubgroup (Fin d → ℤ)} {L : Fin d → ℕ} {k : ℕ} {t : ℝ}
    (hne : ∃ s, 0 ≤ s ∧ HasIndependentShort Λ L k s)
    (h : ∀ s, 0 ≤ s → HasIndependentShort Λ L k s → t ≤ s) : t ≤ successiveMinimum Λ L k :=
  le_csInf hne fun s hs ↦ h s hs.1 hs.2

/-! ### Attainment of the minima

The ratios `|v i| / L i` that a family of integer vectors realizes all have the common denominator
`∏ L`, so the dilation factors that carry an independent family form a set of multiples of
`1 / ∏ L`. Such a set has a least element, which is the discrete substitute for the compactness
argument that attains the minima of a general convex body. -/

/-- The largest coefficient of a family of integer vectors, measured over the common denominator
`∏ L`: it is the numerator of `max (j, i), |v j i| / L i`. -/
def scaledSup (L : Fin d → ℕ) {k : ℕ} (v : Fin k → (Fin d → ℤ)) : ℕ :=
  Finset.univ.sup fun p : Fin k × Fin d ↦ (v p.1 p.2).natAbs * ((∏ i, L i) / L p.2)

lemma le_scaledSup (L : Fin d → ℕ) {k : ℕ} (v : Fin k → (Fin d → ℤ)) (j : Fin k) (i : Fin d) :
    (v j i).natAbs * ((∏ i, L i) / L i) ≤ scaledSup L v :=
  Finset.le_sup (f := fun p : Fin k × Fin d ↦ (v p.1 p.2).natAbs * ((∏ i, L i) / L p.2))
    (Finset.mem_univ (j, i))

lemma prod_pos_of_length_pos {L : Fin d → ℕ} (hL : ∀ i, 0 < L i) :
    (0 : ℝ) < ((∏ i, L i : ℕ) : ℝ) := by
  exact_mod_cast Finset.prod_pos fun i _ ↦ hL i

/-- A family whose scaled supremum is at most `a` is short for the dilation factor `a / ∏ L`. -/
lemma isShort_of_scaledSup_le {L : Fin d → ℕ} {k : ℕ} (hL : ∀ i, 0 < L i)
    {v : Fin k → (Fin d → ℤ)} {a : ℕ} (ha : scaledSup L v ≤ a) (j : Fin k) :
    IsShort L ((a : ℝ) / ((∏ i, L i : ℕ) : ℝ)) (v j) := by
  intro i
  have hnat : (v j i).natAbs * ∏ i, L i ≤ a * L i := by
    rw [← Nat.div_mul_cancel (Finset.dvd_prod_of_mem L (Finset.mem_univ i)), ← mul_assoc]
    exact Nat.mul_le_mul_right _ (le_trans (le_scaledSup L v j i) ha)
  rw [div_mul_eq_mul_div, le_div_iff₀ (prod_pos_of_length_pos hL), ← Int.cast_abs,
    ← Nat.cast_natAbs]
  exact_mod_cast hnat

/-- A family short for the dilation factor `s` has scaled supremum at most `s * ∏ L`. -/
lemma scaledSup_le_mul {L : Fin d → ℕ} {k : ℕ} {v : Fin k → (Fin d → ℤ)} {s : ℝ} (hs : 0 ≤ s)
    (hv : ∀ j, IsShort L s (v j)) : (scaledSup L v : ℝ) ≤ s * ((∏ i, L i : ℕ) : ℝ) := by
  refine le_trans ?_ (Nat.floor_le (mul_nonneg hs (Nat.cast_nonneg _)))
  apply Nat.cast_le.mpr
  apply Finset.sup_le
  intro p _
  apply Nat.le_floor
  have hcancel : ((∏ i, L i : ℕ) : ℝ) = ((L p.2 : ℕ) : ℝ) * (((∏ i, L i) / L p.2 : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' (Finset.dvd_prod_of_mem L (Finset.mem_univ p.2))]
  rw [Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs, hcancel, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hv p.1 p.2) (Nat.cast_nonneg _)

/-- The infimum defining a successive minimum is attained: some family of `k` independent vectors
of `Λ` is short for the dilation factor `successiveMinimum Λ L k` itself. -/
theorem exists_witness_successiveMinimum {Λ : AddSubgroup (Fin d → ℤ)} {L : Fin d → ℕ} {k : ℕ}
    (hL : ∀ i, 0 < L i) (hne : ∃ t, 0 ≤ t ∧ HasIndependentShort Λ L k t) :
    HasIndependentShort Λ L k (successiveMinimum Λ L k) := by
  classical
  have hQ : ∃ a : ℕ, ∃ v : Fin k → (Fin d → ℤ), LinearIndependent ℤ v ∧ (∀ j, v j ∈ Λ) ∧
      scaledSup L v ≤ a := by
    obtain ⟨t, -, v, hindep, hv⟩ := hne
    exact ⟨scaledSup L v, v, hindep, fun j ↦ (hv j).1, le_rfl⟩
  obtain ⟨v₀, hindep₀, hmem₀, hsup₀⟩ := Nat.find_spec hQ
  have hmin : successiveMinimum Λ L k = (Nat.find hQ : ℝ) / ((∏ i, L i : ℕ) : ℝ) := by
    apply le_antisymm (successiveMinimum_le (by positivity)
      ⟨v₀, hindep₀, fun j ↦ ⟨hmem₀ j, isShort_of_scaledSup_le hL hsup₀ j⟩⟩)
    apply le_successiveMinimum hne
    intro s hs hshort
    obtain ⟨v, hindep, hv⟩ := hshort
    rw [div_le_iff₀ (prod_pos_of_length_pos hL)]
    apply le_trans (Nat.cast_le.mpr (Nat.find_min' hQ
      ⟨v, hindep, fun j ↦ (hv j).1, le_rfl⟩))
    exact scaledSup_le_mul hs fun j ↦ (hv j).2
  rw [hmin]
  exact ⟨v₀, hindep₀, fun j ↦ ⟨hmem₀ j, isShort_of_scaledSup_le hL hsup₀ j⟩⟩

end SuccessiveMinima

end

end ChangFreimanRuzsa
