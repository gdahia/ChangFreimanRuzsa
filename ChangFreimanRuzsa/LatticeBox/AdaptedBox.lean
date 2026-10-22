/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GeometryOfNumbers
public import ChangFreimanRuzsa.GapToolkit
import Mathlib.Tactic.Abel

/-! # Centered GAPs of lattice boxes

Let $b_1, \dots, b_s \in \mathbb{Z}^s$ be independent over $\mathbb{Z}$ and let
$m_1, \dots, m_s \in \mathbb{N}$. The centered GAP `centeredBoxGAP b m` has steps $b_i$ and
coefficients $c_i \in [-m_i, m_i]$. It is proper, it contains every point $\sum_i c_i b_i$ with
$|c_i| \le m_i$, and it has at most $\prod_i (2 m_i + 1)$ elements.

## Main statements

* `centeredBoxGAP_proper`: the centered GAP is proper.
* `mem_centeredBoxGAP_of_mem_intBox`: it contains the image of the coefficient box.
* `card_centeredBoxGAP_le`: it has at most $\prod_i (2 m_i + 1)$ elements.
-/

@[expose] public section

namespace ChangFreimanRuzsa

noncomputable section

variable {s : ℕ}

/-- The centered GAP with steps $b_i$ and coefficients $c_i \in [-m_i, m_i]$, where $b$ is
`step`. -/
def centeredBoxGAP (step : Fin s → (Fin s → ℤ)) (m : Fin s → ℕ) : GAP (Fin s → ℤ) :=
  GAP.ofSteps (-∑ i, m i • step i) step fun i ↦ 2 * m i + 1

lemma centeredBoxGAP_gapMap (step : Fin s → (Fin s → ℤ)) (m : Fin s → ℕ)
    (w : (i : Fin s) → Fin (2 * m i + 1)) :
    gapMap (-∑ i, m i • step i) step (fun i ↦ 2 * m i + 1) w =
      stepsHom step (fun i ↦ (w i : ℤ) - (m i : ℤ)) := by
  change
    -∑ i, m i • step i + ∑ i, (w i : ℕ) • step i =
      ∑ i, ((w i : ℤ) - (m i : ℤ)) • step i
  simp only [sub_zsmul, natCast_zsmul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  abel

lemma carrier_centeredBoxGAP (step : Fin s → (Fin s → ℤ)) (m : Fin s → ℕ) :
    (centeredBoxGAP step m).carrier =
      Finset.univ.image (gapMap (-∑ i, m i • step i) step fun i ↦ 2 * m i + 1) :=
  GAP.carrier_ofSteps fun _ ↦ Nat.succ_pos _

lemma dim_centeredBoxGAP_le (step : Fin s → (Fin s → ℤ)) (m : Fin s → ℕ) :
    (centeredBoxGAP step m).dim ≤ s :=
  GAP.dim_ofSteps_le

lemma centeredBoxGAP_proper {step : Fin s → (Fin s → ℤ)} (m : Fin s → ℕ)
    (hinj : Function.Injective (stepsHom step)) :
    (centeredBoxGAP step m).Proper := by
  refine GAP.proper_ofSteps (fun _ ↦ Nat.succ_pos _) ?_
  intro w₁ w₂ hw
  rw [centeredBoxGAP_gapMap step m w₁, centeredBoxGAP_gapMap step m w₂] at hw
  funext i
  apply Fin.ext
  exact_mod_cast sub_left_inj.mp (congr_fun (hinj hw) i)

lemma mem_centeredBoxGAP_of_mem_intBox (step : Fin s → (Fin s → ℤ)) {m : Fin s → ℕ}
    {v : Fin s → ℤ} (hv : v ∈ intBox m) :
    stepsHom step v ∈ (centeredBoxGAP step m).carrier := by
  have hvbox := mem_intBox.mp hv
  rw [carrier_centeredBoxGAP, Finset.mem_image]
  refine ⟨fun i : Fin s ↦ (⟨(v i + m i).toNat, by grind [abs_le]⟩ : Fin (2 * m i + 1)),
    Finset.mem_univ _, ?_⟩
  rw [centeredBoxGAP_gapMap]
  congr with i
  grind [abs_le]

lemma card_centeredBoxGAP_le (step : Fin s → (Fin s → ℤ)) (m : Fin s → ℕ) :
    (centeredBoxGAP step m).carrier.card ≤ ∏ i, (2 * m i + 1) :=
  GAP.card_carrier_ofSteps_le fun _ ↦ Nat.succ_pos _

end

end ChangFreimanRuzsa
