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

Let $K \subseteq \mathbb{R}^s$ be a symmetric convex set containing $0$, and let $E$ be the set
of integer points of $K$. Then every finite set of integer points of $n K$ has at most
$(2n + 1)^s |E|$ elements.

The proof reduces coordinates modulo $2n + 1$. If two integer points $x, y \in n K$ are congruent
modulo $2n + 1$, then $(x - y) / (2n + 1)$ is an integer point of $K$.
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
  have hscale : (2 * n / (2 * n + 1) : ℝ) ∈ Set.Icc 0 1 :=
    ⟨by positivity, div_le_one_of_le₀ (by linarith) (by positivity)⟩
  convert hconv.smul_mem_of_zero_mem h0 hmid hscale using 1
  ext i
  simp only [Pi.smul_apply, Pi.sub_apply, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one]
  field_simp
  ring

lemma residueVector_eq_dvd_sub {N : ℕ} {x y : Fin s → ℤ}
    (hxy : residueVector N x = residueVector N y) (i : Fin s) :
    (N : ℤ) ∣ x i - y i :=
  (ZMod.intCast_eq_intCast_iff_dvd_sub (y i) (x i) N).mp (congr_fun hxy i).symm

lemma quotientDifference_mul {N : ℕ} {x y : Fin s → ℤ}
    (hxy : residueVector N x = residueVector N y) :
    (fun i ↦ (N : ℤ) * quotientDifference N x y i) = x - y := by
  funext i
  exact Int.mul_ediv_cancel' (residueVector_eq_dvd_sub hxy i)

/-- A finite set of lattice points in an integral dilate of a symmetric convex body has at most
`(2 * n + 1) ^ s` times as many points as the original body. -/
lemma card_le_pow_mul_card_of_mem_convex_dilate
    (E T : Finset (Fin s → ℤ)) {K : Set (Fin s → ℝ)}
    (hconv : Convex ℝ K) (h0 : (0 : Fin s → ℝ) ∈ K)
    (hsymm : ∀ x, x ∈ K ↔ -x ∈ K)
    (hE : ∀ v : Fin s → ℤ, v ∈ E ↔ intVectorToReal v ∈ K)
    {n : ℕ} (hT : ∀ v ∈ T, intVectorToReal v ∈ (n : ℝ) • K) :
    T.card ≤ (2 * n + 1) ^ s * E.card := by
  let N := 2 * n + 1
  refine Finset.card_le_mul_card_image_of_maps_to
    (f := residueVector N) (s := T) (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _)
      E.card ?_ |>.trans ?_
  · intro b _
    obtain hfiber | ⟨y, hy⟩ := ({a ∈ T | residueVector N a = b}).eq_empty_or_nonempty
    · simp [hfiber]
    obtain ⟨hyT, rfl⟩ := Finset.mem_filter.mp hy
    apply Finset.card_le_card_of_injOn (quotientDifference N · y)
    · intro x hx
      obtain ⟨hxT, hres⟩ := Finset.mem_filter.mp hx
      rw [Finset.mem_coe, hE]
      have hreal :
          intVectorToReal (quotientDifference N x y) =
            ((N : ℕ) : ℝ)⁻¹ • (intVectorToReal x - intVectorToReal y) := by
        ext i
        change (quotientDifference N x y i : ℝ) = (N : ℝ)⁻¹ * ((x i : ℝ) - (y i : ℝ))
        rw [inv_mul_eq_div, eq_div_iff (by positivity), mul_comm]
        exact_mod_cast congr_fun (quotientDifference_mul hres) i
      rw [hreal]
      exact natCast_smul_sub_div_mem_of_mem_smul hconv h0 hsymm (hT x hxT) (hT y hyT)
    · intro x hx z hz hxz
      obtain ⟨-, hxres⟩ := Finset.mem_filter.mp hx
      obtain ⟨-, hzres⟩ := Finset.mem_filter.mp hz
      have hmul := congr_arg (fun w ↦ fun i ↦ (N : ℤ) * w i) hxz
      rw [quotientDifference_mul hxres, quotientDifference_mul hzres] at hmul
      exact sub_left_inj.mp hmul
  · simp [N, mul_comm]

end

end ChangFreimanRuzsa
