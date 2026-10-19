/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.Properization.AlgebraAndGAPBasics
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Tactic.Positivity.Finset

/-! # Chang's batch packing argument

This file contains the combinatorial packing argument of Chang's proof. Starting from a finite set
$Q$, one repeatedly adjoins a batch $S \subseteq A$ of $m$ elements whose translates of the current
set are pairwise disjoint, so that each step multiplies the size of the current set by $m$. When no
such batch exists, a maximal family of disjoint translates gives $F \subseteq A$ with $|F| < m$ and
$A \subseteq F + (Q' - Q')$, where $Q'$ is the current set.

## Main statements

* `exists_maximal_disjoint_translates`: a maximal family of disjoint translates of $Q$ by elements
  of $A$ covers $A$ by $F + (Q - Q)$.
* `exists_chang_batch_packing`: the batching process terminates when at most $B$ batches can be
  adjoined.
* `GAP.add_binaryListSum_subset_consBinaryList` and `GAP.card_consBinaryList_le`: adjoining one
  binary generator per element of a batch gives a progression that contains the sums with the batch
  and whose size at most doubles with each generator.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open scoped Pointwise

noncomputable section

namespace GAP

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-- Add one coefficient direction to the front of a GAP. -/
def consGenerator (P : GAP G) (originShift step : G) (length : ℕ)
    (hlength : 0 < length) : GAP G where
  dim := P.dim + 1
  carrier :=
    Finset.univ.image (gapMap (P.origin + originShift)
      (Fin.cases step P.step) (Fin.cases length P.length))
  origin := P.origin + originShift
  step := Fin.cases step P.step
  length := Fin.cases length P.length
  length_pos := Fin.cases hlength P.length_pos
  carrier_eq := rfl

/-- A point of `P`, shifted by the new origin and by an allowed multiple of the new step, lies in
the one-generator extension. -/
lemma add_nsmul_mem_consGenerator (P : GAP G) (originShift step : G)
    (length : ℕ) (hlength : 0 < length) {x : G} (hx : x ∈ P.carrier)
    (k : ℕ) (hk : k < length) :
    x + originShift + k • step ∈
      (P.consGenerator originShift step length hlength).carrier := by
  let newLength : Fin (P.dim + 1) → ℕ := Fin.cases length P.length
  let w : (i : Fin (P.dim + 1)) → Fin (newLength i) :=
    @Fin.cases P.dim (fun i ↦ Fin (newLength i))
      (⟨k, by simpa [newLength] using hk⟩ : Fin (newLength 0))
      (fun i ↦ (⟨P.coefficientsFin x i, by
        simp [newLength]⟩ :
          Fin (newLength i.succ)))
  rw [consGenerator, Finset.mem_image]
  refine ⟨w, Finset.mem_univ _, ?_⟩
  rw [gapMap, Fin.sum_univ_succ]
  simp only [w, Fin.cases_zero, Fin.cases_succ]
  rw [← stepsHom_natCast]
  have hcoeff :
      stepsHom P.step (fun i ↦ (P.coefficientsFin x i : ℤ)) =
        x - P.origin :=
    stepHom_coordinateMap P hx
  rw [hcoeff]
  abel

/-- Add a binary coefficient `0, a` to a GAP. -/
def consBinary (P : GAP G) (a : G) : GAP G :=
  P.consGenerator 0 a 2 (by omega)

lemma mem_consBinary (P : GAP G) (a : G) {x : G} (hx : x ∈ P.carrier) :
    x ∈ (P.consBinary a).carrier := by
  simpa [consBinary] using
    P.add_nsmul_mem_consGenerator 0 a 2 (by grind) hx 0 (by grind)

lemma add_mem_consBinary (P : GAP G) (a : G) {x : G} (hx : x ∈ P.carrier) :
    x + a ∈ (P.consBinary a).carrier := by
  simpa [consBinary, one_nsmul] using
    P.add_nsmul_mem_consGenerator 0 a 2 (by grind) hx 1 (by grind)

/-- A coefficient-box GAP containing `P - P`. -/
def differenceHull (P : GAP G) : GAP G :=
  ofData P.dim
    (-∑ i, (P.length i - 1) • P.step i)
    P.step (fun i ↦ 2 * P.length i) fun i ↦ by
      exact Nat.mul_pos (by omega) (P.length_pos i)

lemma sub_carrier_subset_differenceHull (P : GAP G) :
    P.carrier - P.carrier ⊆ P.differenceHull.carrier := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_sub.1 hz
  let w : (i : Fin P.dim) → Fin (2 * P.length i) :=
    fun i ↦ ⟨(P.coefficientsFin x i : ℕ) +
      (P.length i - 1 - P.coefficientsFin y i), by grind [(P.coefficientsFin x i).isLt]⟩
  change x - y ∈
    (ofData P.dim (-∑ i, (P.length i - 1) • P.step i)
      P.step (fun i ↦ 2 * P.length i)
      (fun i ↦ Nat.mul_pos (by omega) (P.length_pos i))).carrier
  convert mem_ofData P.dim
    (-∑ i, (P.length i - 1) • P.step i)
    P.step (fun i ↦ 2 * P.length i)
    (fun i ↦ Nat.mul_pos (by omega) (P.length_pos i)) w using 1
  have hxy :
      ∑ i, (w i : ℕ) • P.step i =
        stepHom P (P.coordinateMap x) - stepHom P (P.coordinateMap y) +
          ∑ i, (P.length i - 1) • P.step i := by
    simp only [stepHom]
    change (∑ i, (w i : ℕ) • P.step i) =
      stepsHom P.step (fun i ↦ ((P.coefficientsFin x i : ℕ) : ℤ)) -
          stepsHom P.step (fun i ↦ ((P.coefficientsFin y i : ℕ) : ℤ)) +
        ∑ i, (P.length i - 1) • P.step i
    rw [stepsHom_natCast P.step (fun i ↦ (P.coefficientsFin x i : ℕ)),
      stepsHom_natCast P.step (fun i ↦ (P.coefficientsFin y i : ℕ)),
      ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    congr with i
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le
      (by grind [(P.coefficientsFin y i).isLt] : (P.coefficientsFin y i : ℕ) ≤ P.length i - 1)
    simp only [w]
    rw [hk, Nat.add_sub_cancel_left, add_nsmul, add_nsmul]
    abel
  change x - y =
    -∑ i, (P.length i - 1) • P.step i +
      ∑ i, (w i : ℕ) • P.step i
  rw [hxy, stepHom_coordinateMap P hx, stepHom_coordinateMap P hy]
  abel

lemma differenceHull_dim (P : GAP G) : P.differenceHull.dim = P.dim := rfl

/-- Repeatedly add binary generators. -/
def consBinaryList (P : GAP G) : List G → GAP G
  | [] => P
  | a :: l => (P.consBinaryList l).consBinary a

/-- All subset sums along a list. -/
def binaryListSum : List G → Finset G
  | [] => {0}
  | a :: l => ({0, a} : Finset G) + binaryListSum l

lemma add_binaryListSum_subset_consBinaryList (P : GAP G) (l : List G) :
    P.carrier + binaryListSum l ⊆ (P.consBinaryList l).carrier := by
  induction l with
  | nil => simp [binaryListSum, consBinaryList, Finset.singleton_zero]
  | cons a l ih =>
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 hz
    obtain ⟨e, he, s, hs, rfl⟩ := Finset.mem_add.1 hy
    have hxs : x + s ∈ (P.consBinaryList l).carrier := ih (Finset.add_mem_add hx hs)
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · simpa [consBinaryList] using (P.consBinaryList l).mem_consBinary _ hxs
    · simpa [consBinaryList, add_assoc, add_comm, add_left_comm] using
        (P.consBinaryList l).add_mem_consBinary e hxs

/-- The number of coefficient choices in a GAP's defining box. -/
def boxVolume (P : GAP G) : ℕ :=
  ∏ i, P.length i

lemma boxVolume_differenceHull (P : GAP G) :
    P.differenceHull.boxVolume = 2 ^ P.dim * P.boxVolume := by
  change (∏ i : Fin P.dim, 2 * P.length i) = 2 ^ P.dim * P.boxVolume
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, boxVolume]

lemma boxVolume_consGenerator (P : GAP G) (originShift step : G)
    (length : ℕ) (hlength : 0 < length) :
    (P.consGenerator originShift step length hlength).boxVolume =
      length * P.boxVolume := by
  rw [boxVolume, boxVolume, consGenerator, Fin.prod_univ_succ]
  rfl

lemma dim_consBinaryList (P : GAP G) (l : List G) :
    (P.consBinaryList l).dim = P.dim + l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [consBinaryList]
      change (P.consBinaryList l).dim + 1 = P.dim + (l.length + 1)
      grind

lemma boxVolume_consBinaryList (P : GAP G) (l : List G) :
    (P.consBinaryList l).boxVolume = 2 ^ l.length * P.boxVolume := by
  induction l with
  | nil => simp [consBinaryList]
  | cons a l ih =>
      rw [consBinaryList, consBinary, boxVolume_consGenerator, ih,
        List.length_cons, pow_succ]
      ring

lemma card_consBinaryList_le (P : GAP G) (l : List G) :
    (P.consBinaryList l).carrier.card ≤ 2 ^ l.length * P.boxVolume := by
  rw [← P.boxVolume_consBinaryList l, boxVolume]
  exact (P.consBinaryList l).card_le_prod_length

end GAP

section MaximalPacking

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-- If $F \subseteq A$ is maximal such that the translates $f + Q$, $f \in F$, are pairwise
disjoint, then $A \subseteq F + (Q - Q)$. This is Ruzsa's covering argument. -/
lemma exists_maximal_disjoint_translates (A Q : Finset G) (hQ : Q.Nonempty) :
    ∃ F ⊆ A, (F : Set G).PairwiseDisjoint (· +ᵥ Q) ∧ A ⊆ F + (Q - Q) := by
  classical
  set C := {F ∈ A.powerset | (SetLike.coe F).PairwiseDisjoint (· +ᵥ Q)}
  obtain ⟨F, hFmax⟩ := C.exists_maximal (Finset.filter_nonempty_iff.mpr
    ⟨∅, Finset.empty_mem_powerset A, by simp⟩)
  simp only [C, Finset.mem_filter, Finset.mem_powerset] at hFmax
  obtain ⟨hFA, hF⟩ := hFmax.prop
  refine ⟨F, hFA, hF, ?_⟩
  intro a ha
  by_cases haF : a ∈ F
  · exact Finset.subset_add_left F hQ.zero_mem_sub haF
  by_cases! H : ∀ b ∈ F, Disjoint (a +ᵥ Q) (b +ᵥ Q)
  · refine (hFmax.not_gt ?_ (Finset.ssubset_insert haF)).elim
    rw [Finset.insert_subset_iff, Finset.coe_insert]
    exact ⟨⟨ha, hFA⟩, hF.insert fun _ hb _ ↦ H _ hb⟩
  obtain ⟨b, hb, hab⟩ := H
  rw [Finset.not_disjoint_iff] at hab
  obtain ⟨c, hca, hcb⟩ := hab
  rw [Finset.mem_vadd_finset] at hca hcb
  obtain ⟨qa, hqa, hqac⟩ := hca
  obtain ⟨qb, hqb, hqbc⟩ := hcb
  change a + qa = c at hqac
  change b + qb = c at hqbc
  refine Finset.mem_add.mpr ⟨b, hb, qb - qa,
    Finset.mem_sub.mpr ⟨qb, hqb, qa, hqa, rfl⟩, ?_⟩
  apply add_right_cancel (b := qa)
  rw [add_assoc, sub_add_cancel, hqbc, hqac]

end MaximalPacking

section BatchPacking

variable {G : Type*} [DecidableEq G] [AddCommGroup G]

/-- The sum of one choice from each batch. -/
def batchSum : List (Finset G) → Finset G
  | [] => {0}
  | S :: batches => S + batchSum batches

/-- A deterministic list containing exactly the elements of a finset. -/
def finsetList (S : Finset G) : List G :=
  S.val.toList

omit [DecidableEq G] [AddCommGroup G] in
@[simp] lemma finsetList_length (S : Finset G) :
    (finsetList S).length = S.card := by
  rw [finsetList, Multiset.length_toList, Finset.card_def]

omit [DecidableEq G] [AddCommGroup G] in
@[simp] lemma mem_finsetList {S : Finset G} {x : G} :
    x ∈ finsetList S ↔ x ∈ S := by
  change x ∈ (↑S.val.toList : Multiset G) ↔ x ∈ S.val
  rw [Multiset.coe_toList]

/-- The concatenation of deterministic enumerations of all batches. -/
def batchElements (batches : List (Finset G)) : List G :=
  batches.flatMap finsetList

omit [DecidableEq G] [AddCommGroup G] in
lemma batchElements_length {batches : List (Finset G)} {m : ℕ}
    (hbatches : ∀ S ∈ batches, S.card = m) :
    (batchElements batches).length = m * batches.length := by
  induction batches with
  | nil => simp [batchElements]
  | cons S batches ih =>
      rw [batchElements, List.flatMap_cons, List.length_append]
      change (finsetList S).length + (batchElements batches).length =
        m * (S :: batches).length
      rw [finsetList_length,
        ih (fun T hT ↦ hbatches T (List.mem_cons_of_mem S hT)),
        List.length_cons, hbatches S List.mem_cons_self]
      ring

lemma zero_mem_binaryListSum (l : List G) :
    0 ∈ GAP.binaryListSum l := by
  induction l with
  | nil => simp [GAP.binaryListSum]
  | cons a l ih =>
      rw [GAP.binaryListSum, Finset.mem_add]
      exact ⟨0, by simp, 0, ih, by simp⟩

lemma mem_binaryListSum_of_mem {l : List G} {x : G} (hx : x ∈ l) :
    x ∈ GAP.binaryListSum l := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
      rw [List.mem_cons] at hx
      rw [GAP.binaryListSum, Finset.mem_add]
      rcases hx with rfl | hx
      · exact ⟨x, by simp, 0, zero_mem_binaryListSum l, by simp⟩
      · exact ⟨0, by simp, x, ih hx, by simp⟩

lemma binaryListSum_append (l₁ l₂ : List G) :
    GAP.binaryListSum (l₁ ++ l₂) =
      GAP.binaryListSum l₁ + GAP.binaryListSum l₂ := by
  induction l₁ with
  | nil =>
      ext x
      simp [GAP.binaryListSum, Finset.mem_add]
  | cons a l₁ ih =>
      rw [List.cons_append, GAP.binaryListSum, GAP.binaryListSum, ih, add_assoc]

lemma batchSum_subset_binaryListSum_batchElements (batches : List (Finset G)) :
    batchSum batches ⊆ GAP.binaryListSum (batchElements batches) := by
  induction batches with
  | nil => simp [batchSum, batchElements, GAP.binaryListSum]
  | cons S batches ih =>
      intro z hz
      obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 hz
      rw [batchElements, List.flatMap_cons, binaryListSum_append, Finset.mem_add]
      exact ⟨x, mem_binaryListSum_of_mem (mem_finsetList.mpr hx),
        y, ih hy, rfl⟩

private lemma add_batchSum_nil (Q : Finset G) : Q + batchSum [] = Q := by
  rw [batchSum, Finset.singleton_zero, add_zero]

private lemma exists_small_cover_or_batch (A Q : Finset G) (hQ : Q.Nonempty) (m : ℕ) :
    (∃ F ⊆ A, F.card < m ∧ A ⊆ F + (Q - Q)) ∨
      ∃ S ⊆ A, S.card = m ∧ (Q + S).card = Q.card * m := by
  obtain ⟨F, hFA, hFdisjoint, hcover⟩ := exists_maximal_disjoint_translates A Q hQ
  obtain h | h := lt_or_ge F.card m
  · exact Or.inl ⟨F, hFA, h, hcover⟩
  right
  obtain ⟨S, hSF, hScard⟩ := Finset.exists_subset_card_eq h
  refine ⟨S, hSF.trans hFA, hScard, ?_⟩
  rw [add_comm, Finset.card_add_iff.mpr (Finset.pairwiseDisjoint_vadd_iff.mp
    (Set.Pairwise.mono (Finset.coe_subset.mpr hSF) hFdisjoint)), hScard, Nat.mul_comm]

/-- Chang's batching process. At every step it chooses $m$ pairwise disjoint translates of the
current set by elements of $A$, so adjoining the chosen batch multiplies its cardinality by $m$.
The ambient group may be infinite. The process terminates because, by hypothesis, at most $B$
batches can be adjoined in this way. -/
lemma exists_chang_batch_packing (A Q : Finset G) (hQ : Q.Nonempty) (m : ℕ) (hm : 0 < m)
    (B : ℕ) (hB : ∀ batches : List (Finset G), (∀ S ∈ batches, S ⊆ A ∧ S.card = m) →
      (Q + batchSum batches).card = Q.card * m ^ batches.length → batches.length ≤ B) :
    ∃ batches : List (Finset G), ∃ F : Finset G,
      (∀ S ∈ batches, S ⊆ A ∧ S.card = m) ∧
      (Q + batchSum batches).card = Q.card * m ^ batches.length ∧
      F ⊆ A ∧ F.card < m ∧
      A ⊆ F + ((Q + batchSum batches) - (Q + batchSum batches)) := by
  obtain ⟨F, hFA, hFcard, hcover⟩ | ⟨S, hSA, hScard, hQS⟩ :=
    exists_small_cover_or_batch A Q hQ m
  · exact ⟨[], F, by simp, by simp [add_batchSum_nil], hFA, hFcard, by rwa [add_batchSum_nil]⟩
  cases B with
  | zero =>
    refine absurd (hB [S] (by simp [hSA, hScard]) ?_) (by simp)
    rw [batchSum, ← add_assoc, add_batchSum_nil, hQS]
    simp
  | succ B =>
    have hrec :=
      exists_chang_batch_packing A (Q + S) (hQ.add (Finset.card_pos.1 (hScard ▸ hm))) m hm B ?_
    · obtain ⟨batches, F, hbatches, hpacked, hFA, hFcard, hcover⟩ := hrec
      refine ⟨S :: batches, F, List.forall_mem_cons.2 ⟨⟨hSA, hScard⟩, hbatches⟩, ?_, hFA,
        hFcard, ?_⟩
      · rw [batchSum, ← add_assoc, hpacked, hQS, List.length_cons, pow_succ]
        ring
      · simpa [batchSum, ← add_assoc] using hcover
    intro batches hbatches hcard
    refine Nat.le_of_succ_le_succ (hB (S :: batches)
      (List.forall_mem_cons.2 ⟨⟨hSA, hScard⟩, hbatches⟩) ?_)
    rw [batchSum, ← add_assoc, hcard, hQS, List.length_cons, pow_succ]
    ring

end BatchPacking

end

end ChangFreimanRuzsa
