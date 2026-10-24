/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GapToolkit
public import ChangFreimanRuzsa.GeometryOfNumbers
public import ChangFreimanRuzsa.IntVectorToReal
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import ChangFreimanRuzsa.ConvexGeometry
import ChangFreimanRuzsa.LatticeBox.AdaptedBox
import ChangFreimanRuzsa.LatticeBox.ConvexCardinality
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Gauge bounds for lattice coefficient boxes

Let `L` be a subgroup of a real normed space `E` and let `K ⊆ E` be a symmetric convex
neighborhood of `0`. Consider linearly independent vectors `b : Fin s → E` in `L` and half-widths
`m : Fin s → ℕ` such that every point of `K ∩ L` is `∑ i, c i • b i` with `c ∈ intBox m`, and
`m i * gauge K (b i) ≤ A` for every `i`. Then every combination `∑ i, c i • b i` with
`c ∈ intBox m` has gauge at most `s * A`. For the lattice `ℤ ^ s ⊆ ℝ ^ s` and `A = a : ℕ`, the
coefficient box therefore maps into `(s * a) • K`, and the residue estimate
`card_le_pow_mul_card_of_mem_convex_dilate` bounds the size of the centered GAP of the box.

The file also defines the gauge bounds `A 0 = 0`, `A (s + 1) = 1 + 4 * s * A s` of the
shortest-vector induction and proves the elementary facts that the induction uses.

## Main definitions

* `latticeBoxGaugeBound`: the gauge bounds `A s`.
* `latticeBoxFactor`: the factor `(2 * (s * A s) + 1) ^ s`.

## Main statements

* `exists_mem_ne_zero_gauge_pos_forall_gauge_le`: a discrete subgroup has a nonzero vector of
  least gauge.
* `exists_proper_gap_card_le_of_gauge_le`: the integer points `D` of `K ⊆ ℝ ^ s` lie in a proper
  GAP of dimension at most `s` with at most `(2 * (s * a) + 1) ^ s * #D` elements.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open scoped Pointwise Topology

open ConvexGeometry Metric

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : ℕ} {K : Set E}

/-- The gauge bounds `A 0 = 0` and `A (s + 1) = 1 + 4 * s * A s` of the shortest-vector
induction. -/
def latticeBoxGaugeBound : ℕ → ℕ
  | 0 => 0
  | s + 1 => 1 + 4 * s * latticeBoxGaugeBound s

/-- The factor `(2 * (s * latticeBoxGaugeBound s) + 1) ^ s`. -/
def latticeBoxFactor (s : ℕ) : ℕ :=
  (2 * (s * latticeBoxGaugeBound s) + 1) ^ s

lemma latticeBoxGaugeBound_le_pow (s : ℕ) :
    latticeBoxGaugeBound s ≤ (4 * s + 1) ^ s := by
  induction s with
  | zero => simp [latticeBoxGaugeBound]
  | succ s ih =>
      rw [latticeBoxGaugeBound, pow_succ]
      nlinarith [Nat.mul_le_mul_left (4 * s)
        (ih.trans (Nat.pow_le_pow_left (by grind : 4 * s + 1 ≤ 4 * (s + 1) + 1) s)),
        (one_le_pow₀ (by grind) : 1 ≤ (4 * (s + 1) + 1) ^ s)]

lemma latticeBoxFactor_le_pow (s : ℕ) :
    latticeBoxFactor s ≤ (4 * s + 1) ^ ((s + 2) * s) := by
  rw [latticeBoxFactor, pow_mul]
  apply Nat.pow_le_pow_left
  rw [pow_add]
  nlinarith [Nat.mul_le_mul_left (2 * s) (latticeBoxGaugeBound_le_pow s),
    Nat.mul_le_mul_left ((4 * s + 1) ^ s) (by nlinarith : 2 * s + 1 ≤ (4 * s + 1) ^ 2),
    (one_le_pow₀ (by grind) : 1 ≤ (4 * s + 1) ^ s)]

/-- If `K ∩ L` spans `E` and `π : E →ₗ[ℝ] F` is surjective, then `π '' K ∩ L.map π` spans `F`. -/
lemma span_inter_image_map_eq_top
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : AddSubgroup E} {π : E →ₗ[ℝ] F} (hπ : Function.Surjective π)
    (hspan : Submodule.span ℝ (K ∩ (L : Set E)) = ⊤) :
    Submodule.span ℝ
      ((π '' K) ∩ ((L.map (π : E →+ F)) : Set F)) = ⊤ := by
  rw [eq_top_iff, ← LinearMap.range_eq_top.mpr hπ, LinearMap.range_eq_map, ← hspan,
    Submodule.map_span]
  apply Submodule.span_mono
  rintro _ ⟨x, ⟨hxK, hxL⟩, rfl⟩
  exact ⟨⟨x, hxK, rfl⟩, AddSubgroup.mem_map_of_mem _ hxL⟩

/-- If `K` is a compact convex neighborhood of `0` and `K ∩ L` spans the nontrivial space `E`,
then `L` has a nonzero point `v` of positive minimal gauge among the nonzero points of `L`. -/
lemma exists_mem_ne_zero_gauge_pos_forall_gauge_le [FiniteDimensional ℝ E] [Nontrivial E]
    {L : AddSubgroup E} [DiscreteTopology L] (hconv : Convex ℝ K)
    (hcompact : IsCompact K) (hK₀ : K ∈ 𝓝 0)
    (hspan : Submodule.span ℝ (K ∩ (L : Set E)) = ⊤) :
    ∃ v ∈ L, v ≠ 0 ∧ 0 < gauge K v ∧ ∀ y ∈ L, y ≠ 0 → gauge K v ≤ gauge K y := by
  obtain ⟨x, ⟨-, hxL⟩, hx₀⟩ : ∃ x ∈ K ∩ (L : Set E), x ≠ 0 := by
    by_contra! h
    exact top_ne_bot (hspan.symm.trans (Submodule.span_eq_bot.mpr h))
  obtain ⟨v, hvL, hv₀, hmin⟩ :=
    exists_mem_ne_zero_forall_gauge_le hconv hcompact.isClosed hK₀ hcompact.isBounded hxL hx₀
  exact ⟨v, hvL, hv₀, (gauge_pos (absorbent_nhds_zero hK₀)
    ((NormedSpace.isVonNBounded_iff ℝ).mpr hcompact.isBounded)).mpr hv₀, hmin⟩

/-- If `m i * gauge K (step i) ≤ A` for every `i`, then every combination `∑ i, c i • step i` with
`c ∈ intBox m` has gauge at most `s * A`. -/
lemma gauge_sum_intCast_smul_le_mul
    (hconv : Convex ℝ K) (hK₀ : K ∈ 𝓝 0) (hsymm : ∀ x ∈ K, -x ∈ K)
    {step : Fin s → E} {m : Fin s → ℕ} {A : ℝ}
    (hend : ∀ i, m i * gauge K (step i) ≤ A)
    {c : Fin s → ℤ} (hc : c ∈ intBox m) :
    gauge K (∑ i, (c i : ℝ) • step i) ≤ s * A := by
  refine (gauge_sum_le hconv (absorbent_nhds_zero hK₀) Finset.univ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ A ?_).trans_eq (by simp)
  intro i _
  rw [gauge_smul ((balanced_iff_neg_mem hconv).mpr hsymm), Real.norm_eq_abs]
  refine (mul_le_mul_of_nonneg_right ?_ (gauge_nonneg (step i))).trans (hend i)
  exact_mod_cast mem_intBox.mp hc i

lemma intVectorToReal_stepsHom (step : Fin s → (Fin s → ℤ)) (c : Fin s → ℤ) :
    intVectorToReal (stepsHom step c) =
      ∑ i, (c i : ℝ) • intVectorToReal (step i) := by
  rw [stepsHom_apply, map_sum]
  congr with i : 1
  rw [map_zsmul, Int.cast_smul_eq_zsmul]

/-- Integer vectors that are linearly independent over `ℝ` are independent over `ℤ`. -/
lemma injective_stepsHom_of_linearIndependent {step : Fin s → (Fin s → ℤ)}
    (h : LinearIndependent ℝ fun i ↦ intVectorToReal (step i)) :
    Function.Injective (stepsHom step) := by
  intro c c' hcc'
  have hreal := congr_arg intVectorToReal hcc'
  rw [intVectorToReal_stepsHom, intVectorToReal_stepsHom] at hreal
  funext i
  simpa [sub_eq_zero] using Fintype.linearIndependent_iff.mp h (fun j ↦ ((c j - c' j : ℤ) : ℝ))
    (by simpa [sub_smul, sub_eq_zero] using hreal) i

/-- Let `K ⊆ ℝ ^ s` be a compact symmetric convex neighborhood of `0` with integer points `D`.
Let `b : Fin s → ℝ ^ s` be linearly independent integer vectors and `m : Fin s → ℕ` such that
every integer point of `K` is `∑ i, c i • b i` with `c ∈ intBox m`, and `m i * gauge K (b i) ≤ a`
for every `i`. Then `D` lies in a proper GAP of dimension at most `s` with at most
`(2 * (s * a) + 1) ^ s * #D` elements. -/
lemma exists_proper_gap_card_le_of_gauge_le {D : Finset (Fin s → ℤ)} {K : Set (Fin s → ℝ)}
    (hconv : Convex ℝ K) (hcompact : IsCompact K) (hK₀ : K ∈ 𝓝 0) (hsymm : ∀ x ∈ K, -x ∈ K)
    (hD : ∀ v, v ∈ D ↔ intVectorToReal v ∈ K) {a : ℕ} {b : Fin s → Fin s → ℝ}
    {m : Fin s → ℕ}
    (hbL : ∀ i, b i ∈ (⊤ : AddSubgroup (Fin s → ℤ)).map intVectorToReal)
    (hb : LinearIndependent ℝ b)
    (hcover : ∀ x ∈ K, x ∈ (⊤ : AddSubgroup (Fin s → ℤ)).map intVectorToReal →
      ∃ c ∈ intBox m, ∑ i, (c i : ℝ) • b i = x)
    (hgauge : ∀ i, m i * gauge K (b i) ≤ a) :
    ∃ P : GAP (Fin s → ℤ), P.Proper ∧ D ⊆ P.carrier ∧ P.dim ≤ s ∧
      P.carrier.card ≤ (2 * (s * a) + 1) ^ s * D.card := by
  choose step _ hstep using fun i ↦ AddSubgroup.mem_map.mp (hbL i)
  obtain rfl : (fun i ↦ intVectorToReal (step i)) = b := funext hstep
  have hinj := injective_stepsHom_of_linearIndependent hb
  refine ⟨centeredBoxGAP step m, centeredBoxGAP_proper m hinj, ?_,
    dim_centeredBoxGAP_le step m, (card_centeredBoxGAP_le step m).trans ?_⟩
  · intro x hx
    obtain ⟨c, hc, hcx⟩ := hcover _ ((hD x).mp hx)
      (AddSubgroup.mem_map_of_mem _ (AddSubgroup.mem_top x))
    obtain rfl := intVectorToReal_injective ((intVectorToReal_stepsHom step c).trans hcx)
    exact mem_centeredBoxGAP_of_mem_intBox step hc
  · rw [← card_intBox, ← Finset.card_image_of_injective _ hinj]
    apply card_le_pow_mul_card_of_mem_convex_dilate hconv (mem_of_mem_nhds hK₀) hsymm hD
    intro v hv
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hv
    rw [mem_smul_iff_gauge_le hconv hcompact.isClosed hK₀
      ((NormedSpace.isVonNBounded_iff ℝ).mpr hcompact.isBounded) (by positivity),
      intVectorToReal_stepsHom]
    exact_mod_cast gauge_sum_intCast_smul_le_mul hconv hK₀ hsymm hgauge hc

end

end ChangFreimanRuzsa
