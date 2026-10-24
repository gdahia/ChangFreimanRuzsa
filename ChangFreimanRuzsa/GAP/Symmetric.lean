/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GAP.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Tactic.Abel

/-!
# Symmetric progressions

Let `x : Fin d → G` be steps in an abelian group and let `L : Fin d → ℕ`. The symmetric
progression `symmetricGAP x L` consists of the combinations `∑ i, n i • x i` with `|n i| ≤ L i`.
It has at most `∏ i, (2 * L i + 1)` elements, with equality when it is proper, and it is proper as
soon as the steps admit no nonzero relation with `|n i| ≤ 2 * L i`.

## Main definitions

* `symmetricGAP x L`: the symmetric progression with steps `x` and half-widths `L`.

## Main statements

* `exists_coeff_of_mem_symmetricGAP` and `stepsHom_mem_symmetricGAP`: the elements of the
  progression are the combinations of its steps with coefficients `|n i| ≤ L i`.
* `proper_symmetricGAP` and `proper_symmetricGAP_of_injective`: conditions for properness.
* `card_symmetricGAP` and `card_symmetricGAP_le`: the number of elements.
-/

@[expose] public section

namespace ChangFreimanRuzsa

noncomputable section

/-- The progression with steps `x` whose `i`-th coefficient `n i` ranges over `|n i| ≤ L i`. -/
def symmetricGAP {G : Type*} [AddCommGroup G] {d : ℕ} (x : Fin d → G)
    (L : Fin d → ℕ) : GAP G :=
  GAP.ofSteps (stepsHom x fun i ↦ -(L i : ℤ)) x fun i ↦ 2 * L i + 1

variable {G : Type*} [AddCommGroup G] {d : ℕ} {x : Fin d → G} {L : Fin d → ℕ}

lemma carrier_symmetricGAP [DecidableEq G] :
    (symmetricGAP x L).carrier =
      Finset.univ.image (gapMap (stepsHom x fun i ↦ -(L i : ℤ)) x fun i ↦ 2 * L i + 1) :=
  GAP.carrier_ofSteps fun _ ↦ Nat.succ_pos _

lemma dim_symmetricGAP_le : (symmetricGAP x L).dim ≤ d :=
  GAP.dim_ofSteps_le

/-- The point of the symmetric progression with coordinates `w` is the combination of its steps
with coefficients `w i - L i`. -/
lemma gapMap_symmetricGAP (w : (i : Fin d) → Fin (2 * L i + 1)) :
    gapMap (stepsHom x fun i ↦ -(L i : ℤ)) x (fun i ↦ 2 * L i + 1) w =
      stepsHom x fun i ↦ (w i : ℤ) - L i := by
  rw [gapMap, stepsHom_apply, stepsHom_apply, ← Finset.sum_add_distrib]
  congr with i
  rw [sub_zsmul, natCast_zsmul, neg_zsmul]
  abel

/-- Every element of the symmetric progression is a combination of its steps with coefficients
`n i` satisfying `|n i| ≤ L i`. -/
lemma exists_coeff_of_mem_symmetricGAP [DecidableEq G] {y : G}
    (hy : y ∈ (symmetricGAP x L).carrier) :
    ∃ n : Fin d → ℤ, (∀ i, |n i| ≤ L i) ∧ y = stepsHom x n := by
  rw [carrier_symmetricGAP] at hy
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hy
  refine ⟨fun i ↦ (w i : ℤ) - L i, ?_, gapMap_symmetricGAP w⟩
  intro i
  rw [abs_le]
  grind [(by simp : (w i : ℕ) < 2 * L i + 1)]

/-- The points of the symmetric progression with distinct coordinates are distinct as soon as its
steps admit no nonzero relation with coefficients in the doubled range. -/
lemma injective_gapMap_symmetricGAP
    (h : ∀ n : Fin d → ℤ, (∀ i, |n i| ≤ 2 * L i) → stepsHom x n = 0 → ∀ i, n i = 0) :
    Function.Injective (gapMap (stepsHom x fun i ↦ -(L i : ℤ)) x fun i ↦ 2 * L i + 1) := by
  intro w w' hww'
  have hrel : stepsHom x
      ((fun i : Fin d ↦ (w i : ℤ) - L i) - fun i : Fin d ↦ (w' i : ℤ) - L i) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact (gapMap_symmetricGAP w).symm.trans (hww'.trans (gapMap_symmetricGAP w'))
  have hbound (i : Fin d) :
      |((fun i : Fin d ↦ (w i : ℤ) - L i) - fun i : Fin d ↦ (w' i : ℤ) - L i) i| ≤ 2 * L i := by
    rw [Pi.sub_apply, abs_le]
    grind [(by simp : (w i : ℕ) < 2 * L i + 1),
      (by simp : (w' i : ℕ) < 2 * L i + 1)]
  funext i
  exact Fin.ext (by grind [h _ hbound hrel i, Pi.sub_apply])

/-- The symmetric progression is proper as soon as its steps admit no nonzero relation with
coefficients in the doubled range. -/
lemma proper_symmetricGAP
    (h : ∀ n : Fin d → ℤ, (∀ i, |n i| ≤ 2 * L i) → stepsHom x n = 0 → ∀ i, n i = 0) :
    (symmetricGAP x L).Proper :=
  GAP.proper_ofSteps (fun _ ↦ Nat.succ_pos _) (injective_gapMap_symmetricGAP h)

lemma card_symmetricGAP [DecidableEq G]
    (h : ∀ n : Fin d → ℤ, (∀ i, |n i| ≤ 2 * L i) → stepsHom x n = 0 → ∀ i, n i = 0) :
    (symmetricGAP x L).carrier.card = ∏ i, (2 * L i + 1) := by
  rw [carrier_symmetricGAP, Finset.card_image_of_injective _ (injective_gapMap_symmetricGAP h)]
  simp


/-- The symmetric progression is proper when its step homomorphism is injective. -/
lemma proper_symmetricGAP_of_injective (hx : Function.Injective (stepsHom x)) :
    (symmetricGAP x L).Proper :=
  proper_symmetricGAP fun n _ hn i ↦ by simp [hx (hn.trans (map_zero _).symm)]

/-- The symmetric progression contains every combination of its steps with coefficients `n i`
satisfying `|n i| ≤ L i`. -/
lemma stepsHom_mem_symmetricGAP [DecidableEq G] {n : Fin d → ℤ} (hn : ∀ i, |n i| ≤ L i) :
    stepsHom x n ∈ (symmetricGAP x L).carrier := by
  rw [carrier_symmetricGAP, Finset.mem_image]
  refine ⟨fun i ↦ ⟨(n i + L i).toNat, by grind [abs_le, hn i]⟩, Finset.mem_univ _, ?_⟩
  rw [gapMap_symmetricGAP]
  congr with i
  grind [abs_le, hn i]

lemma card_symmetricGAP_le [DecidableEq G] :
    (symmetricGAP x L).carrier.card ≤ ∏ i, (2 * L i + 1) :=
  GAP.card_carrier_ofSteps_le fun _ ↦ Nat.succ_pos _

end

end ChangFreimanRuzsa
