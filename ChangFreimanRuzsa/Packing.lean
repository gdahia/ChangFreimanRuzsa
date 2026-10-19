/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GapToolkit
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
import Mathlib.Algebra.BigOperators.Fin
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
* `GAP.consBinary P a`: the progression $P$ with the step $a$ of length $2$ added.
* `GAP.consBinaryList P l`: the progression $P$ with one step of length $2$ added for each entry
  of $l$.
* `GAP.difference P`: a progression containing $P - P$, with the steps of $P$ and doubled lengths.

## Main statements

* `exists_pairwiseDisjoint_vadd_subset_add_sub`: a maximal family of disjoint translates of $Q$ by
  elements of $A$ covers $A$ by $F + (Q - Q)$.
* `exists_card_add_sum_eq_card_mul_pow_and_subset_add_sub`: the packing process stops when at most
  $B$ steps are possible.
* `GAP.add_listSubsetSum_subset_consBinaryList` and `GAP.card_consBinaryList_le`: the progression
  `P.consBinaryList l` contains $P$ plus the subset sums of $l$, and has at most
  $2^{|l|} \prod_i \ell_i$ elements.
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

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-- The progression $P$ with the step $a$ of length $2$ added in front of its steps. It contains
$P + \{0, a\}$. -/
def consBinary (P : GAP G) (a : G) : GAP G where
  dim := P.dim + 1
  carrier := univ.image (gapMap P.origin (Fin.cons a P.step) (Fin.cons 2 P.length))
  origin := P.origin
  step := Fin.cons a P.step
  length := Fin.cons 2 P.length
  length_pos i := by cases i using Fin.cases <;> simp [P.length_pos]
  carrier_eq := rfl

lemma add_nsmul_mem_consBinary {P : GAP G} (a : G) {x : G} (hx : x ∈ P.carrier) {k : ℕ}
    (hk : k < 2) : x + k • a ∈ (P.consBinary a).carrier := by
  obtain ⟨c, hc, rfl⟩ := P.mem_carrier_iff.1 hx
  refine mem_image_gapMap_iff.2 ⟨Fin.cons k c, ?_, ?_⟩
  · intro i
    cases i using Fin.cases <;> simp [hk, hc]
  · simp [Fin.sum_univ_succ]
    abel

lemma add_pair_subset_consBinary (P : GAP G) (a : G) :
    P.carrier + {0, a} ⊆ (P.consBinary a).carrier := by
  intro z hz
  obtain ⟨x, hx, e, he, rfl⟩ := mem_add.1 hz
  simp only [mem_insert, mem_singleton] at he
  obtain rfl | rfl := he
  · simpa using add_nsmul_mem_consBinary _ hx (k := 0) (by grind)
  · simpa using add_nsmul_mem_consBinary _ hx (k := 1) (by grind)

lemma one_lt_length_consBinary {P : GAP G} (h : ∀ i, 1 < P.length i) (a : G)
    (i : Fin (P.dim + 1)) : 1 < (P.consBinary a).length i := by
  cases i using Fin.cases <;> simp [consBinary, h]

/-- The progression $P$ with one step of length $2$ added for each entry of the list $l$. -/
def consBinaryList (P : GAP G) : List G → GAP G
  | [] => P
  | a :: l => (P.consBinaryList l).consBinary a

lemma add_listSubsetSum_subset_consBinaryList (P : GAP G) (l : List G) :
    P.carrier + listSubsetSum l ⊆ (P.consBinaryList l).carrier := by
  induction l with
  | nil => simp [consBinaryList]
  | cons a l ih =>
    rw [listSubsetSum_cons, add_left_comm, add_comm {0, a}]
    exact (add_subset_add_right ih).trans ((P.consBinaryList l).add_pair_subset_consBinary a)

lemma add_subset_consBinaryList_toList {P : GAP G} {S : Finset G} (hS : S ⊆ P.carrier)
    (W : Finset G) : S + W ⊆ (P.consBinaryList W.toList).carrier :=
  (add_subset_add hS fun _ hw ↦ mem_listSubsetSum_of_mem (mem_toList.2 hw)).trans
    (P.add_listSubsetSum_subset_consBinaryList W.toList)

lemma dim_consBinaryList (P : GAP G) (l : List G) :
    (P.consBinaryList l).dim = P.dim + l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [consBinaryList, consBinary, ih, List.length_cons]
    grind

lemma one_lt_length_consBinaryList {P : GAP G} (h : ∀ i, 1 < P.length i) (l : List G)
    (i : Fin (P.consBinaryList l).dim) : 1 < (P.consBinaryList l).length i := by
  induction l with
  | nil => exact h i
  | cons a l ih => exact one_lt_length_consBinary ih a i

/-- A progression containing $P - P$. It has the steps $v_i$ of $P$, the lengths $2 \ell_i$ and
the origin $-\sum_i (\ell_i - 1) v_i$. -/
def difference (P : GAP G) : GAP G where
  dim := P.dim
  carrier := univ.image (gapMap (-∑ i, (P.length i - 1) • P.step i) P.step (2 * P.length ·))
  origin := -∑ i, (P.length i - 1) • P.step i
  step := P.step
  length := (2 * P.length ·)
  length_pos i := by grind [P.length_pos i]
  carrier_eq := rfl

@[simp] lemma dim_difference (P : GAP G) : P.difference.dim = P.dim := rfl

lemma sub_subset_difference (P : GAP G) : P.carrier - P.carrier ⊆ P.difference.carrier := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_sub.1 hz
  obtain ⟨c, hc, rfl⟩ := P.mem_carrier_iff.1 hx
  obtain ⟨c', hc', rfl⟩ := P.mem_carrier_iff.1 hy
  refine mem_image_gapMap_iff.2
    ⟨fun i ↦ c i + (P.length i - 1 - c' i), fun i ↦ by grind [hc i, hc' i], ?_⟩
  have h (i : Fin P.dim) : (P.length i - 1 - c' i) • P.step i =
      (P.length i - 1) • P.step i - c' i • P.step i := by
    rw [sub_nsmul _ (Nat.le_sub_one_of_lt (hc' i)), sub_eq_add_neg]
  simp only [add_nsmul, h, sum_add_distrib, sum_sub_distrib]
  abel

lemma sub_subset_difference_of_subset {P : GAP G} {S : Finset G} (hS : S ⊆ P.carrier) :
    S - S ⊆ P.difference.carrier :=
  (sub_subset_sub hS hS).trans P.sub_subset_difference

lemma one_lt_length_difference (P : GAP G) (i : Fin P.dim) : 1 < P.difference.length i := by
  simp only [difference]
  grind [P.length_pos i]

/-- The number $\prod_i \ell_i$ of coefficient vectors of a GAP. -/
def boxVolume (P : GAP G) : ℕ := ∏ i, P.length i

lemma boxVolume_difference (P : GAP G) : P.difference.boxVolume = 2 ^ P.dim * P.boxVolume := by
  change ∏ i : Fin P.dim, 2 * P.length i = _
  rw [prod_mul_distrib, Fin.prod_const, boxVolume]

lemma boxVolume_consBinary (P : GAP G) (a : G) :
    (P.consBinary a).boxVolume = 2 * P.boxVolume := by
  change ∏ i : Fin (P.dim + 1), Fin.cons 2 P.length i = _
  rw [Fin.prod_cons, boxVolume]

lemma boxVolume_consBinaryList (P : GAP G) (l : List G) :
    (P.consBinaryList l).boxVolume = 2 ^ l.length * P.boxVolume := by
  induction l with
  | nil => simp [consBinaryList]
  | cons a l ih =>
    rw [consBinaryList, boxVolume_consBinary, ih, List.length_cons, pow_succ]
    ring

lemma card_consBinaryList_le (P : GAP G) (l : List G) :
    #(P.consBinaryList l).carrier ≤ 2 ^ l.length * P.boxVolume := by
  rw [← P.boxVolume_consBinaryList l]
  exact (P.consBinaryList l).card_le_prod_length

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
