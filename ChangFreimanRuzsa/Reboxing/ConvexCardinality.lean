/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.ConvexProgression
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Data.ZMod.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Cardinality control for dilates of convex lattice sets

This file proves the elementary residue-class estimate used in box reboxing. If the integer
points of a symmetric convex body are `E`, then any finite set of integer points in its `n`-fold
dilate has cardinality at most `(2 * n + 1) ^ s * E.card`.

The proof reduces coordinates modulo `2 * n + 1`. Two points in the same residue class have a
normalized difference which is again an integer point of the original body.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open scoped Pointwise

noncomputable section

variable {s : ℕ}

/-- Coordinatewise reduction of an integer vector modulo `N`. -/
def residueVector (N : ℕ) (x : Fin s → ℤ) : Fin s → ZMod N :=
  fun i ↦ x i

/-- The coordinatewise integral quotient of a difference by `N`. -/
def quotientDifference (N : ℕ) (x y : Fin s → ℤ) : Fin s → ℤ :=
  fun i ↦ (x i - y i).ediv N

lemma natCast_smul_sub_div_mem_of_mem_smul {K : Set (Fin s → ℝ)}
    (hconv : Convex ℝ K) (h0 : (0 : Fin s → ℝ) ∈ K)
    (hsymm : ∀ x, x ∈ K ↔ -x ∈ K) {n : ℕ} {x y : Fin s → ℝ}
    (hx : x ∈ (n : ℝ) • K) (hy : y ∈ (n : ℝ) • K) :
    ((2 * n + 1 : ℕ) : ℝ)⁻¹ • (x - y) ∈ K := by
  obtain ⟨x₀, hx₀, rfl⟩ := Set.mem_smul_set.mp hx
  obtain ⟨y₀, hy₀, rfl⟩ := Set.mem_smul_set.mp hy
  have hmid : (2 : ℝ)⁻¹ • (x₀ - y₀) ∈ K := by
    convert hconv hx₀ ((hsymm y₀).mp hy₀)
        (by positivity : 0 ≤ (2 : ℝ)⁻¹) (by positivity : 0 ≤ (2 : ℝ)⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1) using 1
    module
  have hscale : (0 : ℝ) ≤ 2 * n / (2 * n + 1) := by positivity
  have hscaleOne : (2 : ℝ) * n / (2 * n + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  convert hconv.smul_mem_of_zero_mem h0 hmid ⟨hscale, hscaleOne⟩ using 1
  ext i
  simp only [Pi.smul_apply, Pi.sub_apply, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one]
  field_simp
  ring

lemma residueVector_eq_dvd_sub {N : ℕ} {x y : Fin s → ℤ}
    (hxy : residueVector N x = residueVector N y) (i : Fin s) :
    (N : ℤ) ∣ x i - y i := by
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub (y i) (x i) N).mp
    (congr_fun hxy i).symm

lemma quotientDifference_mul {N : ℕ} {x y : Fin s → ℤ}
    (hxy : residueVector N x = residueVector N y) :
    (fun i ↦ (N : ℤ) * quotientDifference N x y i) = x - y := by
  funext i
  change (N : ℤ) * ((x i - y i).ediv N) = x i - y i
  rw [mul_comm]
  exact Int.ediv_mul_cancel (residueVector_eq_dvd_sub hxy i)

/-- A finite set of lattice points in an integral dilate of a symmetric convex body has at most
`(2 * n + 1) ^ s` times as many points as the original body. -/
theorem card_le_pow_mul_card_of_mem_convex_dilate
    (E T : Finset (Fin s → ℤ)) {K : Set (Fin s → ℝ)}
    (hconv : Convex ℝ K) (h0 : (0 : Fin s → ℝ) ∈ K)
    (hsymm : ∀ x, x ∈ K ↔ -x ∈ K)
    (hE : ∀ v : Fin s → ℤ, v ∈ E ↔ intVectorToReal v ∈ K)
    {n : ℕ} (hT : ∀ v ∈ T, intVectorToReal v ∈ (n : ℝ) • K) :
    T.card ≤ (2 * n + 1) ^ s * E.card := by
  let N := 2 * n + 1
  let R : Finset (Fin s → ZMod N) := Finset.univ
  refine Finset.card_le_mul_card_image_of_maps_to
    (f := residueVector N) (s := T) (t := R) (fun _ _ ↦ Finset.mem_univ _)
      E.card ?_ |>.trans ?_
  · intro b _
    by_cases hfiber :
        ({a ∈ T | residueVector N a = b} : Finset (Fin s → ℤ)).Nonempty
    swap
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hfiber, Finset.card_empty,
        Nat.zero_le]
    let y := hfiber.choose
    have hy := Finset.mem_filter.mp hfiber.choose_spec
    have hyT : y ∈ T := hy.1
    have hyres : residueVector N y = b := hy.2
    apply Finset.card_le_card_of_injOn (quotientDifference N · y)
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_filter] at hx
      rw [Finset.mem_coe, hE]
      have hres : residueVector N x = residueVector N y := hx.2.trans hyres.symm
      have hreal :
          intVectorToReal (quotientDifference N x y) =
            ((N : ℕ) : ℝ)⁻¹ •
              (intVectorToReal x - intVectorToReal y) := by
        ext i
        change (quotientDifference N x y i : ℝ) =
          (N : ℝ)⁻¹ * ((x i : ℝ) - (y i : ℝ))
        rw [inv_mul_eq_div, eq_div_iff (by positivity : (N : ℝ) ≠ 0)]
        have hi : (N : ℝ) * (quotientDifference N x y i : ℝ) =
            (x i : ℝ) - (y i : ℝ) := by
          exact_mod_cast congr_fun (quotientDifference_mul hres) i
        simpa only [mul_comm] using hi
      rw [hreal]
      exact natCast_smul_sub_div_mem_of_mem_smul hconv h0 hsymm
        (hT x hx.1) (hT y hyT)
    · intro x hx z hz hxz
      rw [Finset.mem_coe, Finset.mem_filter] at hx hz
      have hxres : residueVector N x = residueVector N y := hx.2.trans hyres.symm
      have hzres : residueVector N z = residueVector N y := hz.2.trans hyres.symm
      have hmul := congr_arg (fun w ↦ fun i ↦ (N : ℤ) * w i) hxz
      rw [quotientDifference_mul hxres, quotientDifference_mul hzres] at hmul
      have := congr_arg (· + y) hmul
      simpa only [sub_add_cancel] using this
  · change E.card * Fintype.card (Fin s → ZMod N) ≤ _
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin, N]
    rw [mul_comm]

end

end ChangFreimanRuzsa
