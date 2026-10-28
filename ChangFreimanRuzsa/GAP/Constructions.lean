/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GAP.Basic
import Mathlib.Tactic.Abel

/-!
# Progressions containing subset sums and differences

This file defines the subset sums of a list and progressions containing them, as well as a
progression containing the differences of a progression. Chang's covering argument uses them to
put a set covered by translates in a progression.

## Main definitions

* `listSubsetSum l`: the subset sums of a list `l`, that is, the sum of the sets `{0, a}` for the
  entries `a` of `l`.
* `GAP.consBinary P a`: the progression `P + {0, a}`.
* `GAP.consBinaryList P l`: the progression `P` with one step of length `2` added for each entry
  of `l`.
* `GAP.difference P`: a progression containing `P - P`, the sum of `P` and its reflection
  `GAP.neg P`.

## Main statements

* `GAP.add_listSubsetSum_subset_consBinaryList` and `GAP.size_consBinaryList_le`: the progression
  `P.consBinaryList l` contains `P` plus the subset sums of `l`, and has at most `2 ^ l.length`
  times as many coefficient vectors as `P`.
* `GAP.sub_subset_difference` and `GAP.size_difference_le`: the progression `P.difference`
  contains `P - P` and has at most `2 ^ P.dim` times as many coefficient vectors as `P`.
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
    refine add_subset_add ?_ ih
    intro x hx
    exact mem_listSubsetSum_of_mem (mem_toList.2 hx)

end ListSubsetSum

/-! ## Progressions containing sums and differences -/

namespace GAP

variable {G : Type*} [AddCommGroup G]

/-- The progression `{0, a}`, with the step `a` of length `2`. -/
def pair (a : G) : GAP G := ⟨0, Finsupp.single a 1⟩

lemma pair_subset_toFinset_pair [DecidableEq G] (a : G) : {0, a} ⊆ (pair a).toFinset := by
  rw [insert_subset_iff, singleton_subset_iff]
  constructor
  · simpa [pair] using (pair a).origin_mem
  · simpa [pair, eval] using (pair a).eval_mem_toFinset le_rfl

lemma size_pair (a : G) : (pair a).size = 2 := by
  simp [pair, size]

lemma dim_pair_le (a : G) : (pair a).dim ≤ 1 := by
  classical
  exact (card_le_card Finsupp.support_single_subset).trans_eq (card_singleton a)

/-- The progression `P + {0, a}`: the step `a` of length `2` is added to `P`. -/
def consBinary (P : GAP G) (a : G) : GAP G := P + pair a

lemma add_pair_subset_consBinary [DecidableEq G] (P : GAP G) (a : G) :
    P.toFinset + {0, a} ⊆ (P.consBinary a).toFinset := by
  rw [consBinary, toFinset_add]
  exact add_subset_add_left (pair_subset_toFinset_pair a)

lemma dim_consBinary_le (P : GAP G) (a : G) : (P.consBinary a).dim ≤ P.dim + 1 :=
  (P.dim_add_le _).trans (Nat.add_le_add_left (dim_pair_le a) _)

lemma size_consBinary_le (P : GAP G) (a : G) : (P.consBinary a).size ≤ 2 * P.size := by
  rw [mul_comm, ← size_pair a]
  exact P.size_add_le _

/-- The progression `P` with one step of length `2` added for each entry of the list `l`. -/
def consBinaryList (P : GAP G) : List G → GAP G
  | [] => P
  | a :: l => (P.consBinaryList l).consBinary a

lemma add_listSubsetSum_subset_consBinaryList [DecidableEq G] (P : GAP G) (l : List G) :
    P.toFinset + listSubsetSum l ⊆ (P.consBinaryList l).toFinset := by
  induction l with
  | nil => simp [consBinaryList]
  | cons a l ih =>
    rw [listSubsetSum_cons, add_left_comm, add_comm {0, a}]
    exact (add_subset_add_right ih).trans ((P.consBinaryList l).add_pair_subset_consBinary a)

lemma add_subset_consBinaryList_toList [DecidableEq G] {P : GAP G} {S : Finset G}
    (hS : S ⊆ P.toFinset) (W : Finset G) : S + W ⊆ (P.consBinaryList W.toList).toFinset :=
  (add_subset_add hS fun _ hw ↦ mem_listSubsetSum_of_mem (mem_toList.2 hw)).trans
    (P.add_listSubsetSum_subset_consBinaryList W.toList)

lemma dim_consBinaryList_le (P : GAP G) (l : List G) :
    (P.consBinaryList l).dim ≤ P.dim + l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [consBinaryList, List.length_cons, ← add_assoc]
    exact ((P.consBinaryList l).dim_consBinary_le a).trans (Nat.add_le_add_right ih 1)

lemma size_consBinaryList_le (P : GAP G) (l : List G) :
    (P.consBinaryList l).size ≤ 2 ^ l.length * P.size := by
  induction l with
  | nil => simp [consBinaryList]
  | cons a l ih =>
    rw [consBinaryList, List.length_cons, pow_succ, mul_comm _ 2, mul_assoc]
    exact ((P.consBinaryList l).size_consBinary_le a).trans (Nat.mul_le_mul_left 2 ih)

/-- The reflection `-P` of a progression `P`, with origin `-P.eval P.bound` and the bound of
`P`. -/
def neg (P : GAP G) : GAP G := ⟨-P.eval P.bound, P.bound⟩

lemma neg_toFinset_subset_toFinset_neg [DecidableEq G] (P : GAP G) :
    -P.toFinset ⊆ P.neg.toFinset := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := mem_neg.1 hz
  obtain ⟨c, hc, rfl⟩ := mem_toFinset.1 hx
  obtain ⟨e, he⟩ := exists_add_of_le hc
  refine mem_toFinset.2 ⟨e, le_add_self.trans_eq he.symm, ?_⟩
  simp only [neg, eval_eq_linearCombination, he, map_add]
  abel

/-- A progression containing `P - P`: the sum of `P` and its reflection. It has the steps of `P`
and the bound `2 • P.bound`. -/
def difference (P : GAP G) : GAP G := P + P.neg

lemma sub_subset_difference [DecidableEq G] (P : GAP G) :
    P.toFinset - P.toFinset ⊆ P.difference.toFinset := by
  rw [difference, toFinset_add, sub_eq_add_neg]
  exact add_subset_add_left P.neg_toFinset_subset_toFinset_neg

lemma sub_subset_difference_of_subset [DecidableEq G] {P : GAP G} {S : Finset G}
    (hS : S ⊆ P.toFinset) : S - S ⊆ P.difference.toFinset :=
  (sub_subset_sub hS hS).trans P.sub_subset_difference

lemma dim_difference_le (P : GAP G) : P.difference.dim ≤ P.dim := by
  classical
  rw [difference, dim, bound_add, Finsupp.support_add_eq_union, neg, union_self]
  rfl

lemma size_difference_le (P : GAP G) : P.difference.size ≤ 2 ^ P.dim * P.size :=
  size_add_le_of_bound_eq rfl

end GAP

end

end ChangFreimanRuzsa
