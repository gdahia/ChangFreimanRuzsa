/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GapToolkit
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

/-! # The packing argument of Chang's proof

This file contains the combinatorial packing argument of Chang's proof. Starting from a finite set
$Q$, one repeatedly adds a set $S \subseteq A$ of $m$ elements whose translates of the current set
are pairwise disjoint, so that each step multiplies the size of the current set by $m$. When no
such set exists, a maximal family of disjoint translates gives $F \subseteq A$ with $|F| < m$ and
$A \subseteq F + (Q' - Q')$, where $Q'$ is the current set.

The file also defines progressions containing the sets built in this way.

## Main definitions

* `listSubsetSum l`: the subset sums of a list $a_1, \dots, a_n$, that is,
  $\{0, a_1\} + \dots + \{0, a_n\}$.
* `GAP.consBinary P a`: the progression $P + \{0, a\}$.
* `GAP.consBinaryList P l`: the progression $P$ with one step of length $2$ added for each entry
  of $l$.
* `GAP.difference P`: a progression containing $P - P$, the sum of $P$ and its reflection
  `GAP.neg P`.

## Main statements

* `exists_pairwiseDisjoint_vadd_subset_add_sub`: a maximal family of disjoint translates of $Q$ by
  elements of $A$ covers $A$ by $F + (Q - Q)$.
* `exists_card_add_sum_eq_card_mul_pow_and_subset_add_sub`: the packing process stops when at most
  $B$ steps are possible.
* `GAP.add_listSubsetSum_subset_consBinaryList` and `GAP.size_consBinaryList_le`: the progression
  `P.consBinaryList l` contains $P$ plus the subset sums of $l$, and has at most $2^{|l|}$ times
  as many coefficient vectors as $P$.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open Finset
open scoped Pointwise

noncomputable section

/-! ## Subset sums of a list -/

section ListSubsetSum

variable {G : Type*} [DecidableEq G] [AddCommMonoid G]

/-- The subset sums $\sum_{j \in J} a_j$ of a list $a_1, \dots, a_n$, over all sets $J$ of
positions. It is the sumset $\{0, a_1\} + \dots + \{0, a_n\}$. -/
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
/-- Listing the elements of $k$ sets of $m$ elements each gives a list of length $mk$. -/
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

/-- The progression $\{0, a\}$, with the step $a$ of length $2$. -/
def pair (a : G) : GAP G := ⟨0, Finsupp.single a 1⟩

lemma pair_subset_carrier_pair [DecidableEq G] (a : G) : {0, a} ⊆ (pair a).carrier := by
  rw [insert_subset_iff, singleton_subset_iff]
  constructor
  · simpa [pair] using (pair a).origin_mem
  · simpa [pair, eval] using (pair a).eval_mem_carrier le_rfl

lemma size_pair (a : G) : (pair a).size = 2 := by
  simp [pair, size]

lemma dim_pair_le (a : G) : (pair a).dim ≤ 1 := by
  classical
  exact (card_le_card Finsupp.support_single_subset).trans_eq (card_singleton a)

/-- The progression $P + \{0, a\}$: the step $a$ of length $2$ is added to $P$. -/
def consBinary (P : GAP G) (a : G) : GAP G := P + pair a

lemma add_pair_subset_consBinary [DecidableEq G] (P : GAP G) (a : G) :
    P.carrier + {0, a} ⊆ (P.consBinary a).carrier := by
  rw [consBinary, carrier_add]
  exact add_subset_add_left (pair_subset_carrier_pair a)

lemma dim_consBinary_le (P : GAP G) (a : G) : (P.consBinary a).dim ≤ P.dim + 1 :=
  (P.dim_add_le _).trans (Nat.add_le_add_left (dim_pair_le a) _)

lemma size_consBinary_le (P : GAP G) (a : G) : (P.consBinary a).size ≤ 2 * P.size := by
  rw [mul_comm, ← size_pair a]
  exact P.size_add_le _

/-- The progression $P$ with one step of length $2$ added for each entry of the list $l$. -/
def consBinaryList (P : GAP G) : List G → GAP G
  | [] => P
  | a :: l => (P.consBinaryList l).consBinary a

lemma add_listSubsetSum_subset_consBinaryList [DecidableEq G] (P : GAP G) (l : List G) :
    P.carrier + listSubsetSum l ⊆ (P.consBinaryList l).carrier := by
  induction l with
  | nil => simp [consBinaryList]
  | cons a l ih =>
    rw [listSubsetSum_cons, add_left_comm, add_comm {0, a}]
    exact (add_subset_add_right ih).trans ((P.consBinaryList l).add_pair_subset_consBinary a)

lemma add_subset_consBinaryList_toList [DecidableEq G] {P : GAP G} {S : Finset G}
    (hS : S ⊆ P.carrier) (W : Finset G) : S + W ⊆ (P.consBinaryList W.toList).carrier :=
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

/-- The reflection $-P$ of a progression $P$, with origin $-x_0 - \sum_v b_v v$ and the bound of
$P$. -/
def neg (P : GAP G) : GAP G := ⟨-P.eval P.bound, P.bound⟩

lemma neg_carrier_subset_carrier_neg [DecidableEq G] (P : GAP G) :
    -P.carrier ⊆ P.neg.carrier := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := mem_neg.1 hz
  obtain ⟨c, hc, rfl⟩ := mem_carrier.1 hx
  obtain ⟨e, he⟩ := exists_add_of_le hc
  refine mem_carrier.2 ⟨e, le_add_self.trans_eq he.symm, ?_⟩
  simp only [neg, eval_eq_linearCombination, he, map_add]
  abel

/-- A progression containing $P - P$: the sum of $P$ and its reflection. It has the steps of $P$
and the bound $2 b$. -/
def difference (P : GAP G) : GAP G := P + P.neg

lemma sub_subset_difference [DecidableEq G] (P : GAP G) :
    P.carrier - P.carrier ⊆ P.difference.carrier := by
  rw [difference, carrier_add, sub_eq_add_neg]
  exact add_subset_add_left P.neg_carrier_subset_carrier_neg

lemma sub_subset_difference_of_subset [DecidableEq G] {P : GAP G} {S : Finset G}
    (hS : S ⊆ P.carrier) : S - S ⊆ P.difference.carrier :=
  (sub_subset_sub hS hS).trans P.sub_subset_difference

lemma dim_difference_le (P : GAP G) : P.difference.dim ≤ P.dim := by
  classical
  rw [difference, dim, bound_add, Finsupp.support_add_eq_union, neg, union_self]
  rfl

lemma size_difference_le (P : GAP G) : P.difference.size ≤ 2 ^ P.dim * P.size :=
  size_add_le_of_bound_eq rfl

end GAP

/-! ## The packing argument -/

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-- If $F \subseteq A$ is maximal such that the translates $f + Q$, $f \in F$, are pairwise
disjoint, then $A \subseteq F + (Q - Q)$. This is Ruzsa's covering argument. -/
lemma exists_pairwiseDisjoint_vadd_subset_add_sub (A : Finset G) {Q : Finset G}
    (hQ : Q.Nonempty) :
    ∃ F ⊆ A, (F : Set G).PairwiseDisjoint (· +ᵥ Q) ∧ A ⊆ F + (Q - Q) := by
  classical
  obtain ⟨F, hFmax⟩ := {F ∈ A.powerset | (SetLike.coe F).PairwiseDisjoint (· +ᵥ Q)}.exists_maximal
    ⟨∅, by simp⟩
  simp only [mem_filter, mem_powerset] at hFmax
  obtain ⟨hFA, hF⟩ := hFmax.prop
  refine ⟨F, hFA, hF, ?_⟩
  intro a ha
  by_cases haF : a ∈ F
  · exact subset_add_left F hQ.zero_mem_sub haF
  by_cases! H : ∀ b ∈ F, Disjoint (a +ᵥ Q) (b +ᵥ Q)
  · refine (hFmax.not_gt ?_ (ssubset_insert haF)).elim
    rw [insert_subset_iff, coe_insert]
    exact ⟨⟨ha, hFA⟩, hF.insert fun _ hb _ ↦ H _ hb⟩
  obtain ⟨b, hb, hab⟩ := H
  obtain ⟨c, hca, hcb⟩ := not_disjoint_iff.1 hab
  obtain ⟨qa, hqa, rfl⟩ := mem_vadd_finset.1 hca
  obtain ⟨qb, hqb, hqbc⟩ := mem_vadd_finset.1 hcb
  refine mem_add.2 ⟨b, hb, qb - qa, sub_mem_sub hqb hqa, ?_⟩
  rw [vadd_eq_add, vadd_eq_add] at hqbc
  rw [add_sub, hqbc, add_sub_cancel_right]

/-- Either a maximal family of disjoint translates of $Q$ by elements of $A$ has fewer than $m$
elements, or $A$ contains a set $S$ of $m$ elements with $|Q + S| = |Q| m$. -/
private lemma exists_subset_add_sub_or_card_add_eq (A : Finset G) {Q : Finset G}
    (hQ : Q.Nonempty) (m : ℕ) :
    (∃ F ⊆ A, #F < m ∧ A ⊆ F + (Q - Q)) ∨ ∃ S ⊆ A, #S = m ∧ #(Q + S) = #Q * m := by
  obtain ⟨F, hFA, hF, hcover⟩ := exists_pairwiseDisjoint_vadd_subset_add_sub A hQ
  obtain h | h := lt_or_ge #F m
  · exact Or.inl ⟨F, hFA, h, hcover⟩
  obtain ⟨S, hSF, hS⟩ := exists_subset_card_eq h
  refine Or.inr ⟨S, hSF.trans hFA, hS, ?_⟩
  rw [add_comm, card_add_iff.2 (pairwiseDisjoint_vadd_iff.1 (hF.subset (coe_subset.2 hSF))), hS,
    mul_comm]

private lemma card_add_sum_cons {Q S : Finset G} {m : ℕ} {l : List (Finset G)}
    (hQS : #(Q + S) = #Q * m) (hl : #(Q + S + l.sum) = #(Q + S) * m ^ l.length) :
    #(Q + (S :: l).sum) = #Q * m ^ (S :: l).length := by
  rw [List.sum_cons, ← add_assoc, hl, hQS, List.length_cons, pow_succ]
  ring

/-- The packing argument of Chang's proof. Starting from $Q$, each step adds a set
$S_j \subseteq A$ of $m$ elements whose translates of the current set are pairwise disjoint. If at
most $B$ such steps are possible, then there are sets $S_1, \dots, S_k \subseteq A$ of size $m$
with $|Q + S_1 + \dots + S_k| = |Q| m^k$, and a set $F \subseteq A$ with $|F| < m$ and
$A \subseteq F + (Q' - Q')$, where $Q' = Q + S_1 + \dots + S_k$. The group may be infinite. -/
lemma exists_card_add_sum_eq_card_mul_pow_and_subset_add_sub {A Q : Finset G} (hQ : Q.Nonempty)
    {m : ℕ} (hm : 0 < m) {B : ℕ} (hB : ∀ l : List (Finset G), (∀ S ∈ l, S ⊆ A ∧ #S = m) →
      #(Q + l.sum) = #Q * m ^ l.length → l.length ≤ B) :
    ∃ (l : List (Finset G)) (F : Finset G), (∀ S ∈ l, S ⊆ A ∧ #S = m) ∧
      #(Q + l.sum) = #Q * m ^ l.length ∧ F ⊆ A ∧ #F < m ∧
      A ⊆ F + ((Q + l.sum) - (Q + l.sum)) := by
  obtain ⟨F, hFA, hF, hcover⟩ | ⟨S, hSA, hS, hQS⟩ := exists_subset_add_sub_or_card_add_eq A hQ m
  · exact ⟨[], F, by simp, by simp, hFA, hF, by simpa using hcover⟩
  have hSl {l : List (Finset G)} (hl : ∀ T ∈ l, T ⊆ A ∧ #T = m) :
      ∀ T ∈ S :: l, T ⊆ A ∧ #T = m :=
    List.forall_mem_cons.2 ⟨⟨hSA, hS⟩, hl⟩
  cases B with
  | zero => exact absurd (hB [S] (hSl (by simp)) (by simpa using hQS)) (by simp)
  | succ B =>
    obtain ⟨l, F, hl, hcard, hFA, hF, hcover⟩ :=
      exists_card_add_sum_eq_card_mul_pow_and_subset_add_sub (hQ.add (card_pos.1 (hS ▸ hm))) hm
        (B := B) fun l hl hcard ↦
          Nat.le_of_succ_le_succ (hB _ (hSl hl) (card_add_sum_cons hQS hcard))
    exact ⟨S :: l, F, hSl hl, card_add_sum_cons hQS hcard, hFA, hF,
      by simpa [← add_assoc] using hcover⟩

end

end ChangFreimanRuzsa
