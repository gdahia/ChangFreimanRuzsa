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

This file contains the combinatorial packing part of Chang's proof. It is independent of the
Fourier construction of the initial progression.
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
    P.add_nsmul_mem_consGenerator 0 a 2 (by omega) hx 0 (by omega)

lemma add_mem_consBinary (P : GAP G) (a : G) {x : G} (hx : x ∈ P.carrier) :
    x + a ∈ (P.consBinary a).carrier := by
  simpa [consBinary, one_nsmul] using
    P.add_nsmul_mem_consGenerator 0 a 2 (by omega) hx 1 (by omega)

/-- A coefficient-box GAP containing `P - P`. -/
def differenceHull (P : GAP G) : GAP G :=
  ofData P.dim
    (-∑ i, (P.length i - 1) • P.step i)
    P.step (fun i ↦ 2 * P.length i) fun i ↦ by
      exact Nat.mul_pos (by omega) (P.length_pos i)

lemma sub_carrier_subset_differenceHull (P : GAP G) :
    P.carrier - P.carrier ⊆ P.differenceHull.carrier := by
  intro z hz
  rw [Finset.mem_sub] at hz
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  let w : (i : Fin P.dim) → Fin (2 * P.length i) :=
    fun i ↦ ⟨(P.coefficientsFin x i : ℕ) +
      (P.length i - 1 - P.coefficientsFin y i), by
        have hxi := (P.coefficientsFin x i).isLt
        omega⟩
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
    apply Finset.sum_congr rfl
    intro i _
    have hyi := (P.coefficientsFin y i).isLt
    have hli := P.length_pos i
    simp only [w]
    rw [add_nsmul]
    have hsub :
        P.length i - 1 - (P.coefficientsFin y i : ℕ) +
            (P.coefficientsFin y i : ℕ) =
          P.length i - 1 := by
      omega
    have hmul :
        (P.length i - 1 - (P.coefficientsFin y i : ℕ)) • P.step i +
            (P.coefficientsFin y i : ℕ) • P.step i =
          (P.length i - 1) • P.step i := by
      rw [← add_nsmul, hsub]
    rw [← hmul]
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
  | nil =>
      intro z hz
      rw [binaryListSum, Finset.mem_add] at hz
      obtain ⟨x, hx, y, hy, rfl⟩ := hz
      rw [Finset.mem_singleton] at hy
      simpa [consBinaryList, hy] using hx
  | cons a l ih =>
      intro z hz
      rw [Finset.mem_add] at hz
      obtain ⟨x, hx, y, hy, rfl⟩ := hz
      rw [binaryListSum, Finset.mem_add] at hy
      obtain ⟨e, he, s, hs, rfl⟩ := hy
      rw [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with he | he
      · subst e
        simpa [consBinaryList] using
          (P.consBinaryList l).mem_consBinary a
            (ih (Finset.mem_add.mpr ⟨x, hx, s, hs, rfl⟩))
      · have hxs : x + s ∈ (P.consBinaryList l).carrier :=
          ih (Finset.mem_add.mpr ⟨x, hx, s, hs, rfl⟩)
        subst e
        simpa [consBinaryList, add_assoc, add_comm, add_left_comm] using
          (P.consBinaryList l).add_mem_consBinary a hxs

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
      omega

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

/-- A maximal family of disjoint translates covers the translating set by the difference set of
the packed set. This is the structural part of Ruzsa's covering argument, retaining maximality
rather than replacing it by a cardinal estimate. -/
lemma exists_maximal_disjoint_translates (A Q : Finset G) (hQ : Q.Nonempty) :
    ∃ F ⊆ A, (F : Set G).PairwiseDisjoint (· +ᵥ Q) ∧ A ⊆ F + (Q - Q) := by
  have : ∀ F : Finset G, Decidable ((F : Set G).PairwiseDisjoint (· +ᵥ Q)) :=
    fun F ↦ Classical.dec _
  set C := {F ∈ A.powerset | (SetLike.coe F).PairwiseDisjoint (· +ᵥ Q)}
  obtain ⟨F, hFmax⟩ := C.exists_maximal (Finset.filter_nonempty_iff.mpr
    ⟨∅, Finset.empty_mem_powerset A, by simp⟩)
  simp only [C, Finset.mem_filter, Finset.mem_powerset] at hFmax
  obtain ⟨hFA, hF⟩ := hFmax.1
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
      rcases hx with hx | hx
      · subst x
        exact ⟨a, by simp, 0, zero_mem_binaryListSum l, by simp⟩
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
      rw [batchSum, Finset.mem_add] at hz
      obtain ⟨x, hx, y, hy, rfl⟩ := hz
      rw [batchElements, List.flatMap_cons, binaryListSum_append, Finset.mem_add]
      exact ⟨x, mem_binaryListSum_of_mem (mem_finsetList.mpr hx),
        y, ih hy, rfl⟩

/-- Chang's batching process. At every nonterminal stage it chooses `m` disjoint translates of
the current packed set, so adjoining the chosen batch multiplies its cardinality by exactly `m`.
The process terminates because the packed set grows strictly inside a finite ambient group. -/
theorem exists_chang_batch_packing [Finite G] (A Q : Finset G)
    (hQ : Q.Nonempty) (m : ℕ) (hm : 2 ≤ m) :
    ∃ batches : List (Finset G), ∃ F : Finset G,
      (∀ S ∈ batches, S ⊆ A ∧ S.card = m) ∧
      (Q + batchSum batches).card = Q.card * m ^ batches.length ∧
      F ⊆ A ∧ F.card < m ∧
      A ⊆ F + ((Q + batchSum batches) - (Q + batchSum batches)) := by
  let := Fintype.ofFinite G
  induction hmeasure : Fintype.card G - Q.card using Nat.strong_induction_on generalizing Q with
  | h n ih =>
      obtain ⟨F, hFA, hFdisjoint, hcover⟩ :=
        exists_maximal_disjoint_translates A Q hQ
      by_cases hFcard : F.card < m
      · have hQzero : Q + ({0} : Finset G) = Q := by
          ext x
          simp [Finset.mem_add]
        refine ⟨[], F, ?_, ?_, hFA, hFcard, ?_⟩
        · simp
        · rw [batchSum, hQzero]
          simp
        · simpa only [batchSum, hQzero] using hcover
      · obtain ⟨S, hSF, hScard⟩ :=
          Finset.exists_subset_card_eq (Nat.le_of_not_gt hFcard)
        have hSnonempty : S.Nonempty := by
          rw [← Finset.card_pos, hScard]
          omega
        have hSdisjoint : (S : Set G).PairwiseDisjoint (· +ᵥ Q) :=
          Set.Pairwise.mono (Finset.coe_subset.mpr hSF) hFdisjoint
        have hQScard : (Q + S).card = Q.card * m := by
          rw [add_comm, Finset.card_add_iff.mpr
            (Finset.pairwiseDisjoint_vadd_iff.mp hSdisjoint), hScard, Nat.mul_comm]
        have hQcard : 0 < Q.card := Finset.card_pos.mpr hQ
        have hQScard_strict : Q.card < (Q + S).card := by
          rw [hQScard]
          simpa only [one_mul, Nat.mul_comm] using
            Nat.mul_lt_mul_of_pos_right (show 1 < m by omega) hQcard
        have hnext :
            Fintype.card G - (Q + S).card < Fintype.card G - Q.card := by
          have hQSuniv := Finset.card_le_univ (Q + S)
          omega
        obtain ⟨batches, F', hbatches, hpacked, hF'A, hF'card, hF'cover⟩ :=
          ih (Fintype.card G - (Q + S).card) (by simpa only [hmeasure] using hnext)
            (Q + S) (hQ.add hSnonempty) rfl
        refine ⟨S :: batches, F', ?_, ?_, hF'A, hF'card, ?_⟩
        · intro T hT
          rw [List.mem_cons] at hT
          rcases hT with rfl | hT
          · exact ⟨hSF.trans hFA, hScard⟩
          · exact hbatches T hT
        · rw [batchSum, ← add_assoc, hpacked, hQScard, List.length_cons, pow_succ]
          ring
        · simpa only [batchSum, ← add_assoc] using hF'cover

end BatchPacking

end

end ChangFreimanRuzsa
