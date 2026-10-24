/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.IntVectorToReal
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Data.ZMod.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Cardinality control for dilates of convex lattice sets

Let `K ⊆ ℝ ^ s` be a symmetric convex set containing `0`, and let `E` be the set of integer points
of `K`. Then every finite set of integer points of `n • K` has at most `(2 * n + 1) ^ s * #E`
elements.

The proof reduces coordinates modulo `2 * n + 1`. If two integer points `x, y ∈ n • K` are
congruent modulo `2 * n + 1`, then `(2 * n + 1)⁻¹ • (x - y)` is an integer point of `K`.

## Main statements

* `card_le_pow_mul_card_of_mem_convex_dilate`: the bound `(2 * n + 1) ^ s * #E`.
-/

public section

namespace ChangFreimanRuzsa

open scoped Pointwise

noncomputable section

variable {s : ℕ}

/-- The coordinatewise reduction of an integer vector modulo `N`. -/
def residueVector (N : ℕ) (x : Fin s → ℤ) : Fin s → ZMod N :=
  fun i ↦ x i

/-- The vector of the integer quotients `(x i - y i) / N`. -/
def quotientDifference (N : ℕ) (x y : Fin s → ℤ) : Fin s → ℤ :=
  fun i ↦ (x i - y i).ediv N

/-- If `K` is a symmetric convex set containing `0` and `x, y ∈ n • K`, then
`(2 * n + 1)⁻¹ • (x - y) ∈ K`. -/
lemma inv_smul_sub_mem_of_mem_smul {K : Set (Fin s → ℝ)}
    (hconv : Convex ℝ K) (h0 : (0 : Fin s → ℝ) ∈ K)
    (hsymm : ∀ x ∈ K, -x ∈ K) {n : ℕ} {x y : Fin s → ℝ}
    (hx : x ∈ (n : ℝ) • K) (hy : y ∈ (n : ℝ) • K) :
    ((2 * n + 1 : ℕ) : ℝ)⁻¹ • (x - y) ∈ K := by
  obtain ⟨x₀, hx₀, rfl⟩ := Set.mem_smul_set.mp hx
  obtain ⟨y₀, hy₀, rfl⟩ := Set.mem_smul_set.mp hy
  have hmid : (2 : ℝ)⁻¹ • (x₀ - y₀) ∈ K := by
    convert hconv hx₀ (hsymm y₀ hy₀)
        (by positivity : 0 ≤ (2 : ℝ)⁻¹) (by positivity : 0 ≤ (2 : ℝ)⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1) using 1
    module
  convert hconv.smul_mem_of_zero_mem h0 hmid (t := 2 * n / (2 * n + 1))
    ⟨by positivity, div_le_one_of_le₀ (by linarith) (by positivity)⟩ using 1
  ext i
  simp only [Pi.smul_apply, Pi.sub_apply, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one]
  field_simp
  ring

lemma dvd_sub_of_residueVector_eq {N : ℕ} {x y : Fin s → ℤ}
    (hxy : residueVector N x = residueVector N y) (i : Fin s) :
    (N : ℤ) ∣ x i - y i :=
  (ZMod.intCast_eq_intCast_iff_dvd_sub (y i) (x i) N).mp (congr_fun hxy i).symm

lemma natCast_mul_quotientDifference {N : ℕ} {x y : Fin s → ℤ}
    (hxy : residueVector N x = residueVector N y) :
    (fun i ↦ (N : ℤ) * quotientDifference N x y i) = x - y := by
  funext i
  exact Int.mul_ediv_cancel' (dvd_sub_of_residueVector_eq hxy i)

lemma intVectorToReal_quotientDifference {N : ℕ} (hN : N ≠ 0) {x y : Fin s → ℤ}
    (hxy : residueVector N x = residueVector N y) :
    intVectorToReal (quotientDifference N x y) =
      (N : ℝ)⁻¹ • (intVectorToReal x - intVectorToReal y) := by
  ext i
  simp only [intVectorToReal_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [inv_mul_eq_div, eq_div_iff (by positivity), mul_comm]
  exact_mod_cast congr_fun (natCast_mul_quotientDifference hxy) i

/-- Let `K ⊆ ℝ ^ s` be a symmetric convex set containing `0` and let `E` be the set of integer
points of `K`. A finite set `T` of integer points of `n • K` has at most `(2 * n + 1) ^ s * #E`
elements. -/
lemma card_le_pow_mul_card_of_mem_convex_dilate
    {E T : Finset (Fin s → ℤ)} {K : Set (Fin s → ℝ)}
    (hconv : Convex ℝ K) (h0 : (0 : Fin s → ℝ) ∈ K) (hsymm : ∀ x ∈ K, -x ∈ K)
    (hE : ∀ v : Fin s → ℤ, v ∈ E ↔ intVectorToReal v ∈ K)
    {n : ℕ} (hT : ∀ v ∈ T, intVectorToReal v ∈ (n : ℝ) • K) :
    T.card ≤ (2 * n + 1) ^ s * E.card := by
  refine Finset.card_le_mul_card_image_of_maps_to
    (f := residueVector (2 * n + 1)) (s := T) (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _)
      E.card ?_ |>.trans (by simp [mul_comm])
  intro b _
  obtain hfiber | ⟨y, hy⟩ := ({a ∈ T | residueVector (2 * n + 1) a = b}).eq_empty_or_nonempty
  · simp [hfiber]
  obtain ⟨hyT, rfl⟩ := Finset.mem_filter.mp hy
  apply Finset.card_le_card_of_injOn (quotientDifference (2 * n + 1) · y)
  · intro x hx
    obtain ⟨hxT, hres⟩ := Finset.mem_filter.mp hx
    rw [Finset.mem_coe, hE, intVectorToReal_quotientDifference (by grind) hres]
    exact inv_smul_sub_mem_of_mem_smul hconv h0 hsymm (hT x hxT) (hT y hyT)
  · intro x hx z hz hxz
    obtain ⟨-, hxres⟩ := Finset.mem_filter.mp hx
    obtain ⟨-, hzres⟩ := Finset.mem_filter.mp hz
    refine sub_left_inj.mp (?_ : x - y = z - y)
    rw [← natCast_mul_quotientDifference hxres, ← natCast_mul_quotientDifference hzres]
    simp only at hxz
    rw [hxz]

end

end ChangFreimanRuzsa
