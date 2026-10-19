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
$|c_i| \le m_i$, and it has $\prod_i (2 m_i + 1)$ elements.

## Main statements

* `centeredBoxGAP_proper`: the centered GAP is proper.
* `mem_centeredBoxGAP_of_mem_intBox`: it contains the image of the coefficient box.
* `centeredBoxGAP_card`: it has $\prod_i (2 m_i + 1)$ elements.
-/

@[expose] public section

namespace ChangFreimanRuzsa

noncomputable section

variable {s : ℕ}

/-- The centered GAP with steps $b_i$ and coefficients $c_i \in [-m_i, m_i]$, where $b$ is
`step`. -/
def centeredBoxGAP (step : Fin s → (Fin s → ℤ)) (m : Fin s → ℕ) :
    GAP (Fin s → ℤ) where
  dim := s
  carrier :=
    Finset.univ.image
      (gapMap (-∑ i, m i • step i) step (fun i ↦ 2 * m i + 1))
  origin := -∑ i, m i • step i
  step := step
  length := fun i ↦ 2 * m i + 1
  length_pos := fun _ ↦ by grind
  carrier_eq := rfl

lemma centeredBoxGAP_gapMap (step : Fin s → (Fin s → ℤ)) (m : Fin s → ℕ)
    (w : (i : Fin s) → Fin (2 * m i + 1)) :
    gapMap (centeredBoxGAP step m).origin (centeredBoxGAP step m).step
        (centeredBoxGAP step m).length w =
      stepsHom step (fun i ↦ (w i : ℤ) - (m i : ℤ)) := by
  change
    -∑ i, m i • step i + ∑ i, (w i : ℕ) • step i =
      ∑ i, ((w i : ℤ) - (m i : ℤ)) • step i
  simp only [sub_zsmul, natCast_zsmul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  abel

lemma centeredBoxGAP_proper {step : Fin s → (Fin s → ℤ)} (m : Fin s → ℕ)
    (hinj : Function.Injective (stepsHom step)) :
    (centeredBoxGAP step m).Proper := by
  intro w₁ w₂ hw
  rw [centeredBoxGAP_gapMap step m w₁, centeredBoxGAP_gapMap step m w₂] at hw
  funext i
  apply Fin.ext
  exact_mod_cast sub_left_inj.mp (congr_fun (hinj hw) i)

lemma mem_centeredBoxGAP_of_mem_intBox (step : Fin s → (Fin s → ℤ)) {m : Fin s → ℕ}
    {v : Fin s → ℤ} (hv : v ∈ intBox m) :
    stepsHom step v ∈ (centeredBoxGAP step m).carrier := by
  have hvbox := mem_intBox.mp hv
  rw [(centeredBoxGAP step m).carrier_eq, Finset.mem_image]
  refine ⟨fun i : Fin s ↦ (⟨(v i + m i).toNat, by grind [abs_le]⟩ : Fin (2 * m i + 1)),
    Finset.mem_univ _, ?_⟩
  rw [centeredBoxGAP_gapMap]
  congr with i
  grind [abs_le]

lemma centeredBoxGAP_card {step : Fin s → (Fin s → ℤ)} (m : Fin s → ℕ)
    (hinj : Function.Injective (stepsHom step)) :
    (centeredBoxGAP step m).carrier.card = ∏ i, (2 * m i + 1) := by
  rw [(centeredBoxGAP step m).card_eq_prod_length (centeredBoxGAP_proper m hinj)]
  rfl

end

end ChangFreimanRuzsa
