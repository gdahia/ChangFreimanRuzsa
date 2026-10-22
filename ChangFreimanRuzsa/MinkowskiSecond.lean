/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Minkowski
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-! # Minkowski's second theorem for a weighted sum of squares

Let `B : Matrix (Fin n) (Fin n) ℤ` have nonzero determinant and let `w : Fin n → ℕ` be positive
weights. The lattice of the vectors `B *ᵥ c` with `c : Fin n → ℤ`, with the norm
`x ↦ ∑ j, w j * x j ^ 2`, is a positive definite integral lattice of determinant
`B.det ^ 2 * ∏ j, w j`. Minkowski's second theorem, in the form proved in the Tau Ceti library,
gives `n` linearly independent vectors of this lattice whose norms have product at most
`2 ^ n * n ! * (B.det ^ 2 * ∏ j, w j)`.

The main result is `exists_linearIndependent_prod_weightedNorm_le`.
-/

public section

namespace ChangFreimanRuzsa

open Matrix Module TauCeti
open scoped Nat

variable {n : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} {w : Fin n → ℕ}

/-- The Gram matrix `Bᵀ * diagonal w * B` of the columns of `B` for the form
`x ↦ ∑ j, w j * x j ^ 2`. -/
private def weightedGram (B : Matrix (Fin n) (Fin n) ℤ) (w : Fin n → ℕ) :
    Matrix (Fin n) (Fin n) ℤ :=
  Bᵀ * diagonal (fun j ↦ (w j : ℤ)) * B

private lemma weightedGram_isSymm (B : Matrix (Fin n) (Fin n) ℤ) (w : Fin n → ℕ) :
    (weightedGram B w).IsSymm := by
  simp [Matrix.IsSymm, weightedGram, Matrix.mul_assoc]

private lemma dotProduct_weightedGram_mulVec (c : Fin n → ℤ) :
    c ⬝ᵥ weightedGram B w *ᵥ c = ∑ j, (w j : ℤ) * (B *ᵥ c) j ^ 2 := by
  rw [weightedGram, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose,
    dotProduct]
  congr with j
  rw [mulVec_diagonal]
  ring

private lemma posDef_weightedGram (hB : B.det ≠ 0) (hw : ∀ j, 0 < w j) :
    ((weightedGram B w).map (Int.castRingHom ℚ)).PosDef := by
  have hmap : (weightedGram B w).map (Int.castRingHom ℚ) = (B.map (Int.castRingHom ℚ))ᴴ *
      diagonal (fun j ↦ (w j : ℚ)) * B.map (Int.castRingHom ℚ) := by
    rw [weightedGram, Matrix.map_mul, Matrix.map_mul, conjTranspose_eq_transpose_of_trivial,
      transpose_map, diagonal_map (map_zero _)]
    simp
  rw [hmap]
  exact (PosDef.diagonal (by simpa using hw)).conjTranspose_mul_mul_same
    (mulVec_injective_of_det_ne_zero (by simpa [← Int.cast_det] using hB))

/-- The lattice `ℤ ^ n` with the form `c ↦ ∑ j, w j * (B *ᵥ c) j ^ 2`. -/
private noncomputable def weightedLattice (B : Matrix (Fin n) (Fin n) ℤ) (w : Fin n → ℕ) :
    IntegralLattice (Fin n → ℚ) :=
  IntegralLattice.ofGramMatrix (Pi.basisFun ℚ (Fin n)) (weightedGram B w) (weightedGram_isSymm B w)

private lemma determinant_weightedLattice :
    (weightedLattice B w).determinant = B.det ^ 2 * ∏ j, (w j : ℤ) := by
  rw [weightedLattice, IntegralLattice.determinant_ofGramMatrix, weightedGram, det_mul, det_mul,
    det_transpose, det_diagonal]
  ring

/-- The basis of `weightedLattice B w` given by the standard basis of `ℤ ^ n`. -/
private noncomputable def weightedBasis (B : Matrix (Fin n) (Fin n) ℤ) (w : Fin n → ℕ) :
    Basis (Fin n) ℤ (weightedLattice B w) :=
  IntegralLattice.ofGramMatrix.basis _ _ _

/-- The vector `B *ᵥ c`, where `c` is the coordinate vector of a point of `weightedLattice B w` in
the basis `weightedBasis B w`. -/
private noncomputable def weightedVec (B : Matrix (Fin n) (Fin n) ℤ) (w : Fin n → ℕ) :
    weightedLattice B w →ₗ[ℤ] (Fin n → ℤ) :=
  B.mulVecLin ∘ₗ (weightedBasis B w).equivFun.toLinearMap

private lemma weightedVec_injective (hB : B.det ≠ 0) :
    Function.Injective (weightedVec B w) :=
  (mulVec_injective_of_det_ne_zero hB).comp (weightedBasis B w).equivFun.injective

private lemma integralNorm_weightedLattice (y : weightedLattice B w) :
    (weightedLattice B w).integralNorm y = ∑ j, (w j : ℤ) * weightedVec B w y j ^ 2 := by
  have hform : (weightedLattice B w).integralForm =
      Matrix.toBilin (weightedBasis B w) (weightedGram B w) := by
    rw [← IntegralLattice.gramMatrix_ofGramMatrix (Pi.basisFun ℚ (Fin n)) (weightedGram B w)
      (weightedGram_isSymm B w), IntegralLattice.gramMatrix_eq_toMatrix]
    exact (Matrix.toBilin_toMatrix _ _).symm
  rw [IntegralLattice.integralNorm_apply, hform, Matrix.toBilin_apply]
  refine .trans ?_ (dotProduct_weightedGram_mulVec ((weightedBasis B w).equivFun y))
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

/-- `Gamma (n / 2 + 1) ^ 2 ≤ n !`, by the log-convexity of `Gamma` between `1` and `n + 1`. -/
private lemma gamma_sq_le_factorial (n : ℕ) : Real.Gamma (n / 2 + 1) ^ 2 ≤ n ! := by
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := 1) (t := n + 1)
    (a := 1 / 2) (b := 1 / 2) one_pos (by positivity) (by norm_num) (by norm_num) (by norm_num)
  rw [(by ring : (1 : ℝ) / 2 * 1 + 1 / 2 * (n + 1) = n / 2 + 1), Real.Gamma_one, Real.one_rpow,
    one_mul, Real.Gamma_nat_eq_factorial, ← Real.sqrt_eq_rpow] at h
  exact (pow_le_pow_left₀ (Real.Gamma_pos_of_pos (by positivity)).le h 2).trans_eq
    (Real.sq_sqrt (Nat.cast_nonneg _))

/-- The constant `4 ^ n * Gamma (n / 2 + 1) ^ 2 / π ^ n` of Minkowski's second theorem is at most
`2 ^ n * n !`. -/
private lemma le_of_mul_pi_pow_le {P Δ : ℝ} (hP : 0 ≤ P) (hΔ : 0 ≤ Δ)
    (h : P * Real.pi ^ n ≤ 4 ^ n * Real.Gamma (n / 2 + 1) ^ 2 * Δ) : P ≤ 2 ^ n * n ! * Δ := by
  refine le_of_mul_le_mul_left ?_ (pow_pos zero_lt_two n)
  calc 2 ^ n * P ≤ Real.pi ^ n * P := by gcongr; exact Real.two_le_pi
    _ ≤ 4 ^ n * Real.Gamma (n / 2 + 1) ^ 2 * Δ := by linarith
    _ ≤ 4 ^ n * n ! * Δ := by gcongr; exact gamma_sq_le_factorial n
    _ = 2 ^ n * (2 ^ n * n ! * Δ) := by rw [(by norm_num : (4 : ℝ) = 2 * 2), mul_pow]; ring

/-- **Minkowski's second theorem** for the lattice of the vectors `B *ᵥ c` with `c : Fin n → ℤ`
and the norm `x ↦ ∑ j, w j * x j ^ 2`. There are `n` linearly independent lattice vectors whose
norms have product at most `2 ^ n * n ! * (B.det ^ 2 * ∏ j, w j)`. -/
lemma exists_linearIndependent_prod_weightedNorm_le (hB : B.det ≠ 0) (hw : ∀ j, 0 < w j) :
    ∃ v : Fin n → Fin n → ℤ, LinearIndependent ℤ v ∧ (∀ i, ∃ c, B *ᵥ c = v i) ∧
      ∏ i, ∑ j, (w j : ℝ) * v i j ^ 2 ≤ 2 ^ n * n ! * ((B.det : ℝ) ^ 2 * ∏ j, (w j : ℝ)) := by
  set L := weightedLattice B w
  have hL : L.IsPosDef :=
    (IntegralLattice.isPosDef_ofGramMatrix_iff _ _ _).mpr (posDef_weightedGram hB hw)
  have hn : finrank ℤ L = n := by simpa using finrank_eq_card_basis (weightedBasis B w)
  obtain ⟨x, hx, hnorm⟩ :=
    hL.isPosSemidef.exists_linearIndependent_integralNorm_eq_successiveMinimum
  refine ⟨fun i ↦ weightedVec B w (x (finCongr hn.symm i)), ?_, fun i ↦ ⟨_, rfl⟩, ?_⟩
  · exact (hx.comp _ (finCongr hn.symm).injective).map' _
      (LinearMap.ker_eq_bot.mpr (weightedVec_injective hB))
  · have hprod : ∏ i, (L.successiveMinimum i : ℝ) =
        ∏ i, ∑ j, (w j : ℝ) * weightedVec B w (x (finCongr hn.symm i)) j ^ 2 := by
      rw [← (finCongr hn.symm).prod_comp]
      congr with i
      exact_mod_cast (hnorm _).symm.trans (integralNorm_weightedLattice _)
    have hmink := hL.prod_successiveMinimum_mul_pi_pow_le
    rw [hprod, determinant_weightedLattice] at hmink
    simp only [hn] at hmink
    exact_mod_cast le_of_mul_pi_pow_le (by positivity) (by positivity) hmink

end ChangFreimanRuzsa
