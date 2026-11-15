/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GAP.Basic

/-!
# Progressions of subset sums

This file defines the subset sums of a list and the progressions whose points are a progression
plus the subset sums of a list. Chang's covering argument uses them to put a set covered by
translates in a progression.

## Main definitions

* `listSubsetSum l`: the subset sums of a list `l`, that is, the sum of the sets `{0, a}` for the
  entries `a` of `l`.
* `GAP.consList l P`: the progression `P` with one step of length `2` added for each entry of `l`.

## Main statements

* `GAP.toFinset_consList`: the points of `GAP.consList l P` are `listSubsetSum l + P`.
* `GAP.size_consList`: the progression `GAP.consList l P` has `2 ^ l.length` times as many
  coefficient vectors as `P`.
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

end

end ChangFreimanRuzsa

open ChangFreimanRuzsa
open scoped Pointwise

namespace GAP

/-! ## Progressions of subset sums -/

variable {G : Type*} [AddCommGroup G]

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
@[simp]
lemma toFinset_consList [DecidableEq G] (l : List G) (P : GAP G) :
    (consList l P).toFinset = listSubsetSum l + P.toFinset := by
  induction l with
  | nil => simp
  | cons a l ih => rw [consList_cons, toFinset_cons, ih, listSubsetSum_cons, add_assoc]

lemma size_consList (l : List G) (P : GAP G) : (consList l P).size = 2 ^ l.length * P.size := by
  induction l with
  | nil => simp
  | cons a l ih => rw [consList_cons, size_cons, ih, List.length_cons, pow_succ', mul_assoc]

end GAP
