/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

/-!
# The packing argument of Chang's proof

This file contains the combinatorial packing argument of Chang's proof. Starting from a finite set
`Q`, one repeatedly adds a set `S ⊆ A` of `m` elements whose translates of the current set are
pairwise disjoint, so that each step multiplies the size of the current set by `m`. When no such
set exists, a maximal family of disjoint translates gives `F ⊆ A` with `#F < m` and
`A ⊆ F + (Q' - Q')`, where `Q'` is the current set.

`ChangFreimanRuzsa.GAP.Constructions` defines progressions containing the sets built in this way.

## Main statements

* `exists_pairwiseDisjoint_vadd_subset_add_sub`: a maximal family of disjoint translates of `Q` by
  elements of `A` covers `A` by `F + (Q - Q)`.
* `exists_card_add_sum_eq_card_mul_pow_and_subset_add_sub`: the packing process stops when at most
  `B` steps are possible.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open Finset
open scoped Pointwise

noncomputable section

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-- If `F ⊆ A` is maximal such that the translates `f +ᵥ Q` with `f ∈ F` are pairwise disjoint,
then `A ⊆ F + (Q - Q)`. This is Ruzsa's covering argument. -/
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

/-- Either a maximal family of disjoint translates of `Q` by elements of `A` has fewer than `m`
elements, or `A` contains a set `S` of `m` elements with `#(Q + S) = #Q * m`. -/
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

/-- The packing argument of Chang's proof. Starting from `Q`, each step adds a set `S ⊆ A` of `m`
elements whose translates of the current set are pairwise disjoint. If at most `B` such steps are
possible, then there are a list `l` of subsets of `A` of size `m` with
`#(Q + l.sum) = #Q * m ^ l.length`, and a set `F ⊆ A` with `#F < m` and `A ⊆ F + (Q' - Q')`,
where `Q' = Q + l.sum`. The group may be infinite. -/
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
