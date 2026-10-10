/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GeometryOfNumbers
public import ChangFreimanRuzsa.GapToolkit

/-! # Adapted lattice boxes and their GAPs

An `AdaptedLatticeBox` is the common algebraic output sought from the specialized projection and
slice arguments: a basis of `ℤ^s` together with coordinate half-widths containing the relevant
lattice points. This module packages such data as a proper centered GAP with an exact cardinality
formula. Quantitative product estimates belong to the shape-specific construction of the adapted
box rather than to this neutral packaging layer.
-/

@[expose] public section

namespace ChangFreimanRuzsa

noncomputable section

variable {s : ℕ}

/-- Basis-and-box data sufficient to rebox a finite set of lattice points. -/
structure AdaptedLatticeBox (E : Finset (Fin s → ℤ)) where
  step : Fin s → (Fin s → ℤ)
  halfWidth : Fin s → ℕ
  stepHom_injective : Function.Injective (stepsHom step)
  mem_stepBox : ∀ x ∈ E, ∃ v ∈ intBox halfWidth, stepsHom step v = x

/-- The centered GAP with steps `step i` and coefficient interval `[-m i, m i]`. -/
def centeredBoxGAP (step : Fin s → (Fin s → ℤ)) (m : Fin s → ℕ) :
    GAP (Fin s → ℤ) where
  dim := s
  carrier :=
    Finset.univ.image
      (gapMap (-∑ i, m i • step i) step (fun i ↦ 2 * m i + 1))
  origin := -∑ i, m i • step i
  step := step
  length := fun i ↦ 2 * m i + 1
  length_pos := fun _ ↦ by omega
  carrier_eq := rfl

lemma centeredBoxGAP_gapMap (step : Fin s → (Fin s → ℤ)) (m : Fin s → ℕ)
    (w : (i : Fin s) → Fin (2 * m i + 1)) :
    gapMap (centeredBoxGAP step m).origin (centeredBoxGAP step m).step
        (centeredBoxGAP step m).length w =
      stepsHom step (fun i ↦ (w i : ℤ) - (m i : ℤ)) := by
  change
    -∑ i, m i • step i + ∑ i, (w i : ℕ) • step i =
      ∑ i, ((w i : ℤ) - (m i : ℤ)) • step i
  have hsum :
      (∑ i, ((w i : ℤ) - (m i : ℤ)) • step i) =
        ∑ i, ((w i : ℕ) • step i - m i • step i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [sub_zsmul, natCast_zsmul, natCast_zsmul, sub_eq_add_neg]
  rw [hsum, Finset.sum_sub_distrib]
  abel

lemma centeredBoxGAP_proper (step : Fin s → (Fin s → ℤ)) (m : Fin s → ℕ)
    (hinj : Function.Injective (stepsHom step)) :
    (centeredBoxGAP step m).Proper := by
  intro w₁ w₂ hw
  rw [centeredBoxGAP_gapMap step m w₁, centeredBoxGAP_gapMap step m w₂] at hw
  have hcoords := hinj hw
  funext i
  apply Fin.ext
  have hi := congr_fun hcoords i
  exact_mod_cast sub_left_inj.mp hi

lemma mem_centeredBoxGAP_of_mem_intBox (step : Fin s → (Fin s → ℤ)) (m : Fin s → ℕ)
    {v : Fin s → ℤ} (hv : v ∈ intBox m) :
    stepsHom step v ∈ (centeredBoxGAP step m).carrier := by
  have hvbox := mem_intBox.mp hv
  let w : (i : Fin s) → Fin (2 * m i + 1) := fun i ↦
    ⟨(v i + m i).toNat, by
      have hi := abs_le.mp (hvbox i)
      rw [Int.toNat_lt]
      · omega
      · linarith⟩
  rw [(centeredBoxGAP step m).carrier_eq, Finset.mem_image]
  refine ⟨w, Finset.mem_univ _, ?_⟩
  rw [centeredBoxGAP_gapMap]
  congr 1
  funext i
  dsimp only [w]
  have hi := abs_le.mp (hvbox i)
  rw [Int.toNat_of_nonneg (by omega)]
  omega

lemma centeredBoxGAP_card (step : Fin s → (Fin s → ℤ)) (m : Fin s → ℕ)
    (hinj : Function.Injective (stepsHom step)) :
    (centeredBoxGAP step m).carrier.card = ∏ i, (2 * m i + 1) := by
  rw [(centeredBoxGAP step m).card_eq_prod_length
    (centeredBoxGAP_proper step m hinj)]
  rfl

/-- An adapted lattice box gives a proper centered GAP with the same coordinate-box cardinality. -/
theorem AdaptedLatticeBox.exists_proper_centeredBoxGAP {E : Finset (Fin s → ℤ)}
    (B : AdaptedLatticeBox E) :
    ∃ P : GAP (Fin s → ℤ), P.Proper ∧ E ⊆ P.carrier ∧ P.dim = s ∧
      P.carrier.card = ∏ i, (2 * B.halfWidth i + 1) := by
  refine ⟨centeredBoxGAP B.step B.halfWidth,
    centeredBoxGAP_proper B.step B.halfWidth B.stepHom_injective, ?_, rfl, ?_⟩
  · intro x hxE
    obtain ⟨v, hvbox, rfl⟩ := B.mem_stepBox x hxE
    exact mem_centeredBoxGAP_of_mem_intBox B.step B.halfWidth hvbox
  · exact centeredBoxGAP_card B.step B.halfWidth B.stepHom_injective

end

end ChangFreimanRuzsa
