/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GAP.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Tactic.Abel

/-!
# Symmetric progressions

Let `x : Fin d → G` be steps in an abelian group and let `L : Fin d → ℕ`. The symmetric
progression `GAP.symmetric x L` consists of the combinations `∑ i, n i • x i` with `|n i| ≤ L i`.
Its size is `∏ i, (2 * L i + 1)`, and it is proper as soon as the steps admit no nonzero relation
with `|n i| ≤ 2 * L i`.

## Main definitions

* `GAP.symmetric x L`: the symmetric progression with steps `x` and half-widths `L`.

## Main statements

* `GAP.mem_symmetric`: the elements of the progression are the combinations of its steps with
  coefficients `|n i| ≤ L i`.
* `GAP.proper_symmetric`: a condition for properness.
* `GAP.nsmul_symmetric`: the multiple `t • GAP.symmetric x L` is `GAP.symmetric x (t • L)`.
-/

@[expose] public section

namespace ChangFreimanRuzsa

noncomputable section

namespace GAP

/-- The progression with steps `x` whose `i`-th coefficient `n i` ranges over `|n i| ≤ L i`. -/
def symmetric {G : Type*} [AddCommGroup G] {d : ℕ} (x : Fin d → G) (L : Fin d → ℕ) : GAP G :=
  ⟨d, stepsHom x fun i ↦ -(L i : ℤ), x, fun i ↦ 2 * L i⟩

variable {G : Type*} [AddCommGroup G] {d : ℕ} {x : Fin d → G} {L : Fin d → ℕ}

@[simp] lemma dim_symmetric : (symmetric x L).dim = d := rfl

lemma size_symmetric : (symmetric x L).size = ∏ i, (2 * L i + 1) := rfl

/-- The point of the symmetric progression with coefficients `w` is the combination of its steps
with coefficients `w i - L i`. -/
private lemma eval_symmetric (w : Fin (symmetric x L).dim → ℕ) :
    (symmetric x L).eval w = stepsHom x fun i ↦ (w i : ℤ) - L i := by
  dsimp only [symmetric, eval]
  rw [stepsHom_apply, stepsHom_apply, ← Finset.sum_add_distrib]
  congr with i
  rw [sub_zsmul, natCast_zsmul, neg_zsmul]
  abel

/-- The elements of the symmetric progression are the combinations of its steps with coefficients
`n i` satisfying `|n i| ≤ L i`. -/
lemma mem_symmetric [DecidableEq G] {y : G} :
    y ∈ (symmetric x L : Finset G) ↔ ∃ n : Fin d → ℤ, (∀ i, |n i| ≤ L i) ∧ stepsHom x n = y := by
  rw [mem_toFinset]
  constructor
  · rintro ⟨w, hw : ∀ i, w i ≤ 2 * L i, rfl⟩
    exact ⟨fun i ↦ (w i : ℤ) - L i, fun i ↦ by grind [abs_le, hw i], (eval_symmetric w).symm⟩
  · rintro ⟨n, hn, rfl⟩
    refine ⟨fun i ↦ (n i + L i).toNat, fun i ↦ (by grind [abs_le, hn i] : _ ≤ 2 * L i), ?_⟩
    rw [eval_symmetric]
    congr with i
    grind [abs_le, hn i]

/-- The symmetric progression is proper as soon as its steps admit no nonzero relation with
coefficients in the doubled range. -/
lemma proper_symmetric
    (h : ∀ n : Fin d → ℤ, (∀ i, |n i| ≤ 2 * L i) → stepsHom x n = 0 → ∀ i, n i = 0) :
    (symmetric x L).Proper := by
  rintro w (hw : ∀ i, w i ≤ 2 * L i) w' (hw' : ∀ i, w' i ≤ 2 * L i) hww'
  have hrel : stepsHom x
      ((fun i : Fin d ↦ (w i : ℤ) - L i) - fun i : Fin d ↦ (w' i : ℤ) - L i) = 0 := by
    rw [map_sub, sub_eq_zero, ← eval_symmetric, ← eval_symmetric]
    exact hww'
  funext i
  grind [h _ (fun j ↦ by grind [abs_le, Pi.sub_apply, hw j, hw' j]) hrel i, Pi.sub_apply]

/-- The multiple `t • GAP.symmetric x L` is the symmetric progression with the same steps and the
half-widths `t * L i`. -/
lemma nsmul_symmetric (t : ℕ) : t • symmetric x L = symmetric x (t • L) := by
  refine congrArg₂ (fun o b ↦ (⟨d, o, x, b⟩ : GAP G)) ?_ ?_ <;> dsimp only [symmetric]
  · rw [← map_nsmul]
    congr with i
    simp
  · funext i
    exact mul_left_comm _ _ _

end GAP

end

end ChangFreimanRuzsa
