/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GeometryOfNumbers
public import ChangFreimanRuzsa.Lattice

/-!
# Saturated spans of integer vectors

The saturated span `saturatedSpan S` of a finite set `S` of vectors of `ℤ ^ d` is the set of
integer vectors in the real span of `S`. It is a saturated submodule of `ℤ ^ d`: it contains every
integer vector with a nonzero multiple in it.

## Main statements

* `finrank_saturatedSpan`: the rank of the saturated span is the dimension of the real span.
* `mem_saturatedSpan_of_zsmul_mem`: the saturated span is saturated.
* `exists_congr_close_isShort` and `exists_congr_span_isShort`: if `v : Fin r → ℤ ^ d` satisfies
  `|v j i| ≤ t * L i`, then every integer vector in its real span is congruent modulo
  `Submodule.span ℤ (Set.range v)` to a vector `y` with `|y i| ≤ r * (t * L i)`.
-/

public section

namespace ChangFreimanRuzsa

noncomputable section

variable {d r : ℕ}

/-- The real span of an independent finite family of integer vectors has the expected
dimension. -/
lemma finrank_integerGeneratedSubspace_image {v : Fin r → (Fin d → ℤ)}
    (hv : LinearIndependent ℤ v) :
    Module.finrank ℝ (integerGeneratedSubspace (Finset.univ.image v)) = r := by
  rw [integerGeneratedSubspace_image_univ,
    finrank_span_eq_card (linearIndependent_intVectorToReal_iff.mpr hv), Fintype.card_fin]

/-- The saturated span and the integer lattice in its real span are the same free
`ℤ`-module. -/
def saturatedSpanEquivSubspaceIntegerLattice (S : Finset (Fin d → ℤ)) :
    saturatedSpan S ≃ₗ[ℤ] subspaceIntegerLattice (integerGeneratedSubspace S) := by
  refine LinearEquiv.ofBijective
    { toFun v := ⟨⟨intVectorToReal v, v.prop⟩,
        intVectorToReal_mem_standardIntegerLattice (v : Fin d → ℤ)⟩
      map_add' x y := by
        ext1
        ext1
        exact map_add intVectorToReal (x : Fin d → ℤ) y
      map_smul' c x := by
        ext1
        ext1
        exact map_zsmul intVectorToReal c (x : Fin d → ℤ) } ⟨?_, ?_⟩
  · intro x y hxy
    rw [Subtype.ext_iff, Subtype.ext_iff] at hxy
    exact Subtype.ext (intVectorToReal_injective hxy)
  · rintro ⟨⟨x, hx⟩, hxL⟩
    obtain ⟨v, rfl⟩ := exists_intVectorToReal_of_mem_standardIntegerLattice
      (mem_standardIntegerLattice_of_mem_subspaceIntegerLattice hxL)
    exact ⟨⟨v, hx⟩, rfl⟩

lemma finrank_saturatedSpan (S : Finset (Fin d → ℤ)) :
    Module.finrank ℤ (saturatedSpan S) = Module.finrank ℝ (integerGeneratedSubspace S) := by
  rw [(saturatedSpanEquivSubspaceIntegerLattice S).finrank_eq,
    finrank_subspaceIntegerLattice_integerGeneratedSubspace]

/-- The saturated span is saturated: if a nonzero multiple of `v` lies in it, so does `v`. -/
lemma mem_saturatedSpan_of_zsmul_mem {S : Finset (Fin d → ℤ)} {v : Fin d → ℤ} {c : ℤ}
    (hc : c ≠ 0) (hcv : c • v ∈ saturatedSpan S) :
    v ∈ saturatedSpan S := by
  have hmem := (integerGeneratedSubspace S).smul_mem (c : ℝ)⁻¹ (mem_saturatedSpan.mp hcv)
  rwa [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, inv_smul_smul₀ (by exact_mod_cast hc)] at hmem

/-- If `|v j i| ≤ t * L i` for all `j` and `|a j| ≤ 1`, then
`|∑ j, a j * v j i| ≤ r * (t * L i)`. -/
lemma abs_sum_mul_le_of_isShort {L : Fin d → ℕ} {t : ℝ} {v : Fin r → (Fin d → ℤ)}
    (hshort : ∀ j, IsShort L t (v j)) {a : Fin r → ℝ} (ha : ∀ j, |a j| ≤ 1) (i : Fin d) :
    |∑ j, a j * v j i| ≤ r * (t * L i) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_card_nsmul _ _ (t * L i) ?_).trans_eq (by simp))
  intro j _
  rw [abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) (ha j)).trans (hshort j i)

/-- Let `v : Fin r → ℤ ^ d` be integer vectors with `|v j i| ≤ t * L i`. If `z - b` lies in the
real span of the `v j` for an integer vector `z` and a real vector `b`, then `z` is congruent
modulo `Submodule.span ℤ (Set.range v)` to an integer vector `y` with
`|y i| ≤ |b i| + r * (t * L i)` for all `i`. -/
lemma exists_congr_close_isShort {L : Fin d → ℕ} {t : ℝ} {v : Fin r → (Fin d → ℤ)}
    (hshort : ∀ j, IsShort L t (v j)) {z : Fin d → ℤ} {b : Fin d → ℝ}
    (hspan : intVectorToReal z - b ∈ Submodule.span ℝ (Set.range fun j ↦ intVectorToReal (v j))) :
    ∃ y : Fin d → ℤ, z - y ∈ Submodule.span ℤ (Set.range v) ∧
      ∀ i, |(y i : ℝ)| ≤ |b i| + r * (t * L i) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hspan
  refine ⟨z - ∑ j, round (c j) • v j, ?_, ?_⟩
  · rw [sub_sub_cancel]
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · intro i
    have hy : ((z - ∑ j, round (c j) • v j) i : ℝ) =
        b i + ∑ j, (c j - round (c j)) * v j i := by
      have hci := congr_fun hc i
      simp only [intVectorToReal_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.sub_apply] at hci
      push_cast [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul,
        Finset.sum_sub_distrib]
      linarith
    rw [hy]
    exact (abs_add_le _ _).trans (add_le_add_right (abs_sum_mul_le_of_isShort hshort
      (fun j ↦ (abs_sub_round (c j)).trans (by norm_num)) i) _)

/-- Let `v : Fin r → ℤ ^ d` be integer vectors with `|v j i| ≤ t * L i`. Every integer vector `x`
in their real span is congruent modulo `Submodule.span ℤ (Set.range v)` to an integer vector `y`
with `|y i| ≤ r * (t * L i)` for all `i`. -/
lemma exists_congr_span_isShort {L : Fin d → ℕ} {t : ℝ} {v : Fin r → (Fin d → ℤ)}
    (hshort : ∀ j, IsShort L t (v j)) {x : Fin d → ℤ}
    (hx : x ∈ saturatedSpan (Finset.univ.image v)) :
    ∃ y : Fin d → ℤ, x - y ∈ Submodule.span ℤ (Set.range v) ∧
      ∀ i, |(y i : ℝ)| ≤ r * (t * L i) := by
  rw [mem_saturatedSpan, integerGeneratedSubspace_image_univ, ← sub_zero (intVectorToReal x)] at hx
  simpa using exists_congr_close_isShort hshort hx

end

end ChangFreimanRuzsa
