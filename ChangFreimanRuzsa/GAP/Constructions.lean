/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GAP.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Progressions of subset sums and of differences

This file defines the subset sums of a list, progressions whose points are a progression plus the
subset sums of a list, and a progression whose points are the differences of two points of a
progression. Chang's covering argument uses them to put a set covered by translates in a
progression.

## Main definitions

* `listSubsetSum l`: the subset sums of a list `l`, that is, the sum of the sets `{0, a}` for the
  entries `a` of `l`.
* `GAP.cons a P`: the progression `P` with the step `a` of length `2` added in front.
* `GAP.consList l P`: the progression `P` with one step of length `2` added for each entry of `l`.
* `GAP.difference P`: the progression with the steps of `P`, the bound `2 • P.bound` and the origin
  `-∑ i, P.bound i • P.step i`.

## Main statements

* `GAP.toFinset_cons` and `GAP.toFinset_consList`: the points of `GAP.cons a P` are
  `{0, a} + P`, and those of `GAP.consList l P` are `listSubsetSum l + P`.
* `GAP.size_consList`: the progression `GAP.consList l P` has `2 ^ l.length` times as many
  coefficient vectors as `P`.
* `GAP.toFinset_difference` and `GAP.size_difference_le`: the points of `P.difference` are
  `P - P`, and it has at most `2 ^ P.dim` times as many coefficient vectors as `P`.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open Finset
open scoped Pointwise

noncomputable section

/-! ## Subset sums of a list -/

section ListSubsetSum

variable {G : Type*} [DecidableEq G] [AddCommMonoid G]

/-- The subset sums of a list `l`, over all sets of positions. It is the sum of the sets `{0, a}`
for the entries `a` of `l`. -/
def listSubsetSum (l : List G) : Finset G :=
  (l.map fun a ↦ ({0, a} : Finset G)).sum

@[simp] lemma listSubsetSum_nil : listSubsetSum ([] : List G) = 0 := rfl

lemma listSubsetSum_cons (a : G) (l : List G) :
    listSubsetSum (a :: l) = {0, a} + listSubsetSum l := by
  simp [listSubsetSum]

lemma listSubsetSum_append (l₁ l₂ : List G) :
    listSubsetSum (l₁ ++ l₂) = listSubsetSum l₁ + listSubsetSum l₂ := by
  simp [listSubsetSum]

lemma zero_mem_listSubsetSum (l : List G) : 0 ∈ listSubsetSum l := by
  induction l with
  | nil => simp [listSubsetSum]
  | cons a l ih =>
    rw [listSubsetSum_cons]
    simpa using add_mem_add (mem_insert_self 0 {a}) ih

lemma mem_listSubsetSum_of_mem {l : List G} {x : G} (hx : x ∈ l) : x ∈ listSubsetSum l := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rw [listSubsetSum_cons]
    obtain rfl | hx := List.mem_cons.1 hx
    · simpa using add_mem_add (by simp : x ∈ ({0, x} : Finset G)) (zero_mem_listSubsetSum l)
    · simpa using add_mem_add (by simp : 0 ∈ ({0, a} : Finset G)) (ih hx)

/-- The elements of a finset are subset sums of the list of its elements. -/
lemma subset_listSubsetSum_toList (S : Finset G) : S ⊆ listSubsetSum S.toList := by
  intro x hx
  exact mem_listSubsetSum_of_mem (mem_toList.2 hx)

omit [DecidableEq G] [AddCommMonoid G] in
/-- Listing the elements of `k` sets of `m` elements each gives a list of length `m * k`. -/
lemma length_flatMap_toList {l : List (Finset G)} {m : ℕ} (hl : ∀ S ∈ l, #S = m) :
    (l.flatMap Finset.toList).length = m * l.length := by
  rw [List.length_flatMap, List.map_congr_left (g := fun _ ↦ m) (by simpa using hl),
    List.map_const', List.sum_replicate, smul_eq_mul, mul_comm]

/-- A sum of one element from each set of a list of sets is a subset sum of the list of all their
elements. -/
lemma sum_subset_listSubsetSum_flatMap_toList (l : List (Finset G)) :
    l.sum ⊆ listSubsetSum (l.flatMap Finset.toList) := by
  induction l with
  | nil => simp
  | cons S l ih =>
    rw [List.sum_cons, List.flatMap_cons, listSubsetSum_append]
    exact add_subset_add (subset_listSubsetSum_toList S) ih

end ListSubsetSum

namespace GAP

/-! ## Progressions of subset sums -/

section Cons

variable {G : Type*} [AddCommMonoid G]

/-- The progression `P` with the step `a` of length `2` added in front. Its points are
`{0, a} + P`. -/
def cons (a : G) (P : GAP G) : GAP G :=
  ⟨P.dim + 1, P.origin, Fin.cons a P.step, Fin.cons 1 P.bound⟩

@[simp] lemma dim_cons (a : G) (P : GAP G) : (cons a P).dim = P.dim + 1 := rfl

private lemma eval_cons (a : G) (P : GAP G) (n : ℕ) (w : Fin P.dim → ℕ) :
    (cons a P).eval (Fin.cons n w) = n • a + P.eval w := by
  unfold cons
  simp only [eval, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  exact add_left_comm _ _ _

/-- The points of `GAP.cons a P` are `{0, a} + P`. -/
@[simp, norm_cast]
lemma toFinset_cons [DecidableEq G] (a : G) (P : GAP G) :
    (cons a P : Finset G) = {0, a} + P := by
  ext x
  simp only [mem_toFinset, mem_add, mem_insert, mem_singleton]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨n, u, rfl⟩ : ∃ (n : ℕ) (u : Fin P.dim → ℕ), Fin.cons n u = w :=
      ⟨_, _, Fin.cons_self_tail w⟩
    obtain ⟨hn, hu⟩ := Fin.cons_le_cons.1 hw
    refine ⟨n • a, ?_, _, ⟨u, hu, rfl⟩, (eval_cons ..).symm⟩
    obtain rfl | rfl := Nat.le_one_iff_eq_zero_or_eq_one.1 hn <;> simp
  · rintro ⟨_, rfl | rfl, _, ⟨w, hw, rfl⟩, rfl⟩
    · exact ⟨Fin.cons 0 w, Fin.cons_le_cons.2 ⟨zero_le_one, hw⟩, (eval_cons ..).trans (by simp)⟩
    · exact ⟨Fin.cons 1 w, Fin.cons_le_cons.2 ⟨le_rfl, hw⟩, (eval_cons ..).trans (by simp)⟩

lemma size_cons (a : G) (P : GAP G) : (cons a P).size = 2 * P.size := by
  unfold cons
  simp [size, Fin.prod_univ_succ]

/-- The progression `P` with one step of length `2` added for each entry of the list `l`. Its
points are `listSubsetSum l + P`. -/
def consList (l : List G) (P : GAP G) : GAP G := l.foldr cons P

@[simp] lemma consList_nil (P : GAP G) : consList [] P = P := rfl

@[simp] lemma consList_cons (a : G) (l : List G) (P : GAP G) :
    consList (a :: l) P = cons a (consList l P) := rfl

lemma dim_consList (l : List G) (P : GAP G) : (consList l P).dim = P.dim + l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [consList_cons, dim_cons, ih, List.length_cons, add_assoc]

/-- The points of `GAP.consList l P` are `listSubsetSum l + P`. -/
@[simp, norm_cast]
lemma toFinset_consList [DecidableEq G] (l : List G) (P : GAP G) :
    (consList l P : Finset G) = listSubsetSum l + P := by
  induction l with
  | nil => simp
  | cons a l ih => rw [consList_cons, toFinset_cons, ih, listSubsetSum_cons, add_assoc]

lemma size_consList (l : List G) (P : GAP G) : (consList l P).size = 2 ^ l.length * P.size := by
  induction l with
  | nil => simp
  | cons a l ih => rw [consList_cons, size_cons, ih, List.length_cons, pow_succ', mul_assoc]

end Cons

/-! ## The progression of differences -/

variable {G : Type*} [AddCommGroup G]

/-- The progression with the steps of `P`, the bound `2 • P.bound` and the origin
`-∑ i, P.bound i • P.step i`. Its points are `P - P`. -/
def difference (P : GAP G) : GAP G :=
  ⟨P.dim, -∑ i, P.bound i • P.step i, P.step, 2 • P.bound⟩

lemma dim_difference (P : GAP G) : P.difference.dim = P.dim := rfl

/-- The point of `P.difference` with coefficients `w` is the difference of the points of `P` with
coefficients `u` and `v` when `w + v = u + P.bound`. -/
private lemma eval_difference_eq_sub (P : GAP G) {u v w : Fin P.dim → ℕ}
    (h : ∀ i, w i + v i = u i + P.bound i) : P.difference.eval w = P.eval u - P.eval v := by
  unfold difference
  simp only [eval]
  rw [add_sub_add_left_eq_sub, neg_add_eq_sub, sub_eq_sub_iff_add_eq_add]
  simp only [← sum_add_distrib, ← add_nsmul, h]

/-- The points of `P.difference` are the differences of two points of `P`. -/
@[simp, norm_cast]
lemma toFinset_difference [DecidableEq G] (P : GAP G) : (P.difference : Finset G) = P - P := by
  ext x
  simp only [mem_toFinset, mem_sub]
  constructor
  · rintro ⟨w, hw : ∀ i, w i ≤ 2 * P.bound i, rfl⟩
    refine ⟨_, ⟨fun i ↦ min (w i) (P.bound i), fun i ↦ min_le_right _ _, rfl⟩, _,
      ⟨fun i ↦ P.bound i + min (w i) (P.bound i) - w i, fun i ↦ by grind, rfl⟩,
      (eval_difference_eq_sub P fun i ↦ by grind [hw i]).symm⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨u + (P.bound - v),
      fun i ↦ (by grind [Pi.add_apply, Pi.sub_apply, hu i, hv i] : _ ≤ 2 * P.bound i),
      eval_difference_eq_sub P fun i ↦ by grind [Pi.add_apply, Pi.sub_apply, hv i]⟩

lemma size_difference_le (P : GAP G) : P.difference.size ≤ 2 ^ P.dim * P.size := by
  dsimp only [difference, size]
  rw [← Fin.prod_const, ← prod_mul_distrib]
  gcongr
  simp [mul_add]

end GAP

end

end ChangFreimanRuzsa
