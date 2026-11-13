/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GeometryOfNumbers.IntegerLattice
import Mathlib.Data.Pi.Interval
import Mathlib.MeasureTheory.Integral.Average

/-!
# Counting lattice points by volume

The integer points `latticePoints K` of a set `K ⊆ ℝ ^ n` are compared with the volume of `K`. The
cube `[0, 1) ^ n` is a fundamental domain of `ℤ ^ n`, so the volume of a measurable set `S` is the
integral over the cube of the number of integer translates `v + x` of a point `x` that lie in `S`.
If every point has at least `N` such translates, then `N ≤ volume S`. Some point has at least
`volume S` of them, and their differences are integer points of `S - S`, so
`volume S ≤ #(latticePoints (S - S))`. For a symmetric convex `K` this is the theorem of van der
Corput, `volume K ≤ #(latticePoints (2 • K))`.

## Main definitions

* `latticePoints K`: the integer vectors whose real cast lies in `K`.

## Main statements

* `card_le_volume_of_forall_exists_add_mem`: if every point of `ℝ ^ n` has `#T` integer translates
  in `S`, then `#T ≤ volume S`.
* `volume_le_encard_latticePoints_sub`: `volume S ≤ (latticePoints (S - S)).encard`.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open MeasureTheory Finset
open scoped ENNReal Pointwise

noncomputable section

variable {n : ℕ}

/-- The integer points of a set `K ⊆ ℝ ^ n`: the integer vectors whose real cast lies in `K`. -/
def latticePoints (K : Set (Fin n → ℝ)) : Set (Fin n → ℤ) := intVectorToReal ⁻¹' K

@[simp] lemma mem_latticePoints {K : Set (Fin n → ℝ)} {v : Fin n → ℤ} :
    v ∈ latticePoints K ↔ intVectorToReal v ∈ K := Iff.rfl

lemma latticePoints_mono {K L : Set (Fin n → ℝ)} (h : K ⊆ L) : latticePoints K ⊆ latticePoints L :=
  Set.preimage_mono h

/-- A bounded set has finitely many integer points. -/
lemma finite_latticePoints {K : Set (Fin n → ℝ)} (hK : Bornology.IsBounded K) :
    (latticePoints K).Finite := by
  obtain ⟨R, hR⟩ := hK.exists_norm_le
  refine (Set.finite_Icc (fun _ : Fin n ↦ -⌈R⌉) fun _ ↦ ⌈R⌉).subset fun v hv ↦ ?_
  have h (i : Fin n) : |v i| ≤ ⌈R⌉ := by
    have := (norm_le_pi_norm (intVectorToReal v) i).trans (hR _ hv)
    rw [intVectorToReal_apply, Real.norm_eq_abs] at this
    exact (Int.cast_le (R := ℝ)).1 (by push_cast; linarith [Int.le_ceil R])
  exact ⟨fun i ↦ (abs_le.1 (h i)).1, fun i ↦ (abs_le.1 (h i)).2⟩

/-- The fundamental domain `[0, 1) ^ n` of the integer lattice. -/
local notation "cube" => ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin n))

/-- The integer lattice, as a subgroup acting on `ℝ ^ n` by translation. -/
private abbrev intLattice (n : ℕ) : AddSubgroup (Fin n → ℝ) :=
  (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))).toAddSubgroup

local notation "Λ" => intLattice n

private instance : Countable (intLattice n) :=
  inferInstanceAs (Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))))

private lemma volume_cube : volume cube = 1 := by
  rw [ZSpan.fundamentalDomain_pi_basisFun, Real.volume_pi_Ico]
  simp

/-- The volume of a measurable set `S` is the integral over the cube `[0, 1) ^ n` of the number of
integer translates of a point that lie in `S`. -/
private lemma lintegral_cube_tsum_indicator {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) :
    ∫⁻ x in cube, ∑' g : Λ, S.indicator 1 (g +ᵥ x) = volume S := by
  rw [lintegral_tsum (f := fun (g : Λ) x ↦ S.indicator 1 (g +ᵥ x)) fun g ↦
    ((measurable_one.indicator hS).comp (measurable_const_vadd g)).aemeasurable,
    ← (ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin n)) volume).lintegral_eq_tsum'',
    lintegral_indicator_one hS]

/-- The integer vector `v`, as an element of the integer lattice. -/
private def toLattice (v : Fin n → ℤ) : Λ :=
  ⟨intVectorToReal v, intVectorToReal_mem_standardIntegerLattice v⟩

private lemma toLattice_injective : Function.Injective (toLattice (n := n)) :=
  fun _ _ h ↦ intVectorToReal_injective (congr_arg Subtype.val h)

/-- If every point `x` of `ℝ ^ n` has integer translates `v - z + x`, for `v ∈ T`, in a measurable
set `S`, then `#T ≤ volume S`. -/
lemma card_le_volume_of_forall_exists_add_mem {S : Set (Fin n → ℝ)} (hS : MeasurableSet S)
    (T : Finset (Fin n → ℤ))
    (h : ∀ x, ∃ z : Fin n → ℤ, ∀ v ∈ T, intVectorToReal (v - z) + x ∈ S) :
    (#T : ℝ≥0∞) ≤ volume S := by
  rw [← lintegral_cube_tsum_indicator hS]
  refine le_trans ?_ (setLIntegral_mono' (ZSpan.fundamentalDomain_measurableSet _)
    (f := fun _ ↦ (#T : ℝ≥0∞)) fun x _ ↦ ?_)
  · rw [setLIntegral_const, volume_cube, mul_one]
  obtain ⟨z, hz⟩ := h x
  have hT : ∀ v ∈ T, S.indicator 1 (toLattice (v - z) +ᵥ x) = (1 : ℝ≥0∞) :=
    fun v hv ↦ Set.indicator_of_mem (hz v hv) _
  calc (#T : ℝ≥0∞) = ∑ v ∈ T, S.indicator 1 (toLattice (v - z) +ᵥ x) := by
        rw [sum_congr rfl hT]
        simp
    _ = ∑ g ∈ T.image fun v ↦ toLattice (v - z), S.indicator 1 (g +ᵥ x) := by
        rw [sum_image fun _ _ _ _ h ↦ sub_left_injective (toLattice_injective h)]
    _ ≤ _ := sum_le_tsum _

/-- Two elements of the integer lattice differ by an integer vector. -/
private lemma exists_intVectorToReal_eq_sub (g g₀ : Λ) :
    ∃ v : Fin n → ℤ, intVectorToReal v = (g : Fin n → ℝ) - g₀ :=
  exists_intVectorToReal_of_mem_standardIntegerLattice (sub_mem g.2 g₀.2)

/-- The volume of a measurable set `S` of finite volume is at most the number of integer points of
`S - S`. Some point `x` has at least `volume S` integer translates in `S`, and the differences of
these translates are integer points of `S - S`. -/
lemma volume_le_encard_latticePoints_sub {S : Set (Fin n → ℝ)} (hS : MeasurableSet S)
    (hS' : volume S ≠ ∞) : volume S ≤ (latticePoints (S - S)).encard := by
  have : IsProbabilityMeasure (volume.restrict cube) :=
    ⟨by rw [Measure.restrict_apply_univ, volume_cube]⟩
  obtain ⟨x, hx⟩ := exists_lintegral_le (μ := volume.restrict cube)
    (f := fun x ↦ ∑' g : Λ, S.indicator 1 (g +ᵥ x)) (by rwa [lintegral_cube_tsum_indicator hS])
  rw [lintegral_cube_tsum_indicator hS] at hx
  refine hx.trans ?_
  set A : Set Λ := (· +ᵥ x) ⁻¹' S
  have hA : ∑' g : Λ, S.indicator 1 (g +ᵥ x) = (A.encard : ℝ≥0∞) := by
    rw [← ENNReal.tsum_set_one]
    exact (_root_.tsum_subtype A 1).symm
  rw [hA]
  rcases A.eq_empty_or_nonempty with hA₀ | ⟨g₀, hg₀⟩
  · simp [hA₀]
  choose v hv using fun g : Λ ↦ exists_intVectorToReal_eq_sub g g₀
  refine ENat.toENNReal_le.2 (Set.encard_le_encard_of_injOn (f := v) (fun g hg ↦ ?_) ?_)
  · rw [mem_latticePoints, hv]
    refine ⟨_, hg, _, hg₀, ?_⟩
    simp only [AddSubgroup.vadd_def, vadd_eq_add]
    abel
  · intro g _ g' _ h
    have := congr_arg intVectorToReal h
    rw [hv, hv, sub_left_inj] at this
    exact Subtype.ext this

end

end ChangFreimanRuzsa
