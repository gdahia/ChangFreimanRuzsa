/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GeometryOfNumbers.GaugeBox
import ChangFreimanRuzsa.GeometryOfNumbers.Gauge
import ChangFreimanRuzsa.GeometryOfNumbers.RealBox

/-!
# Shortest-vector induction for lattice boxes with gauge bounds

Let `E` be a real normed space of dimension `n`, let `L` be a discrete subgroup of `E`, and let
`K ⊆ E` be a compact symmetric convex neighborhood of `0` such that `K ∩ L` spans `E`. Then there
are linearly independent `b : Fin n → E` in `L` and `m : Fin n → ℕ` such that every point of
`K ∩ L` is `∑ i, c i • b i` with `c ∈ intBox m`, and `m i * gauge K (b i) ≤ latticeBoxGaugeBound n`.

The proof is by induction on `n`. Choose a nonzero `v ∈ L` of minimal gauge and project `E` onto a
complement `W` of `ℝ ∙ v`. The induction hypothesis gives vectors and half-widths for the
projections of `L` and `K` in `W`. Each vector lifts to a vector of `L` of at most twice its gauge,
and `v` is added as a new vector whose half-width covers the multiples of `v` that remain.

## Main statements

* `exists_linearIndependent_mem_intBox_gauge_le`: the vectors and half-widths with gauge bound
  `latticeBoxGaugeBound n`.
* `exists_proper_gap_of_convex_body`: the integer points of a compact symmetric convex
  neighborhood of `0` in `ℝ ^ s` whose integer points span `ℝ ^ s` lie in a proper GAP of
  dimension at most `s` with at most `latticeBoxFactor s` times as many elements.
-/

public section

namespace ChangFreimanRuzsa

open scoped Pointwise Topology

open ConvexGeometry Metric Module

noncomputable section

universe u

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {L : AddSubgroup E} {K : Set E}

/-- The projection of a discrete subgroup `L` along a line `ℝ ∙ v` with `v ∈ L` is discrete. -/
lemma discreteTopology_map_projectionOnto [FiniteDimensional ℝ E] [DiscreteTopology L] {v : E}
    (hvL : v ∈ L) {W : Submodule ℝ E} (hcompl : IsCompl W (ℝ ∙ v)) :
    DiscreteTopology (L.map (W.projectionOnto (ℝ ∙ v) hcompl : E →+ W)) := by
  obtain ⟨r, hr, h⟩ := exists_pos_forall_le_norm_apply hvL
    (Submodule.projection_apply_of_mem_right hcompl (Submodule.mem_span_singleton_self v))
    fun y ↦ (Submodule.mem_span_singleton.mp (Submodule.sub_projection_mem hcompl y)).imp
      fun _ ↦ Eq.symm
  refine DiscreteTopology.of_forall_le_norm hr ?_
  rintro ⟨_, hx⟩ hne
  obtain ⟨y, hyL, rfl⟩ := AddSubgroup.mem_map.mp hx
  exact h y hyL fun hy ↦ hne (Subtype.ext (Subtype.ext hy))

lemma finrank_eq_of_isCompl_span_singleton [FiniteDimensional ℝ E] {n : ℕ} {v : E} (hv₀ : v ≠ 0)
    {W : Submodule ℝ E} (hcompl : IsCompl W (ℝ ∙ v)) (hrank : finrank ℝ E = n + 1) :
    finrank ℝ W = n := by
  grind [Submodule.finrank_add_eq_of_isCompl hcompl, finrank_span_singleton (K := ℝ) hv₀]

/-- Let `v ∈ L` be a nonzero vector of least gauge and let `π` be a linear map with kernel
`ℝ ∙ v`. A nonzero vector `w` of `L.map π` lifts to a vector of `L` whose gauge is at most twice
`gauge (π '' K) w`. -/
lemma exists_mem_apply_eq_gauge_le_two_mul (hconv : Convex ℝ K) (hK₀ : K ∈ 𝓝 0)
    (hsymm : ∀ x ∈ K, -x ∈ K) {π : E →ₗ[ℝ] F} {v : E} (hvL : v ∈ L) (hπv : π v = 0)
    (hker : ∀ x, π x = 0 → ∃ s : ℝ, x = s • v) (hmin : ∀ y ∈ L, y ≠ 0 → gauge K v ≤ gauge K y)
    (hKπ : IsCompact (π '' K)) (hKπ₀ : π '' K ∈ 𝓝 0) {w : F} (hwL : w ∈ L.map (π : E →+ F))
    (hw₀ : w ≠ 0) :
    ∃ y ∈ L, π y = w ∧ gauge K y ≤ 2 * gauge (π '' K) w := by
  have hwK : w ∈ gauge (π '' K) w • (π '' K) :=
    (mem_smul_iff_gauge_le (hconv.linear_image π) hKπ.isClosed hKπ₀
      ((NormedSpace.isVonNBounded_iff ℝ).mpr hKπ.isBounded) (gauge_nonneg w) w).mpr le_rfl
  obtain ⟨y, hyL, hyw, hy⟩ :=
    exists_mem_gauge_le_of_mem_map hconv hK₀ hsymm hvL hπv hker (gauge_nonneg w) hwL hwK
  refine ⟨y, hyL, hyw, ?_⟩
  linarith [gauge_le_two_mul_of_mem_map hconv hK₀ hsymm hvL hπv hker hmin (gauge_nonneg w) hwL hw₀
    hwK]

/-- If `π v = 0`, `v ≠ 0` and the images `π (y i)` are linearly independent, then `Fin.cons v y`
is linearly independent. -/
lemma linearIndependent_finCons_of_apply_eq_zero {n : ℕ} {π : E →ₗ[ℝ] F} {v : E} (hv₀ : v ≠ 0)
    (hπv : π v = 0) {y : Fin n → E} {b : Fin n → F} (hyb : ∀ i, π (y i) = b i)
    (hb : LinearIndependent ℝ b) :
    LinearIndependent ℝ (Fin.cons v y : Fin (n + 1) → E) := by
  obtain rfl : π ∘ y = b := funext hyb
  refine linearIndependent_finCons.mpr ⟨hb.of_comp, ?_⟩
  intro hv
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
  apply hv₀
  simp [← hc, Fintype.linearIndependent_iff.mp hb c (by simpa [hπv] using congr_arg π hc)]

/-- Let `v ∈ L` be a nonzero vector of least gauge and let `π` be a linear map with kernel
`ℝ ∙ v`. Suppose that every point of `π '' K ∩ L.map π` is `∑ i, c i • b i` with `c ∈ intBox m`,
and that `y i ∈ L` lifts `b i` with `m i * gauge K (y i) ≤ B`. Then every `x ∈ K ∩ L` is
`k • v + ∑ i, c i • y i` with `k : ℤ`, `c ∈ intBox m` and `|k| * gauge K v ≤ 1 + n * B`. -/
lemma exists_intCast_smul_add_sum_eq (hconv : Convex ℝ K) (hK₀ : K ∈ 𝓝 0)
    (hsymm : ∀ x ∈ K, -x ∈ K) {π : E →ₗ[ℝ] F} {v : E} (hvL : v ∈ L) (hvpos : 0 < gauge K v)
    (hmin : ∀ y ∈ L, y ≠ 0 → gauge K v ≤ gauge K y) (hker : ∀ x, π x = 0 → ∃ s : ℝ, x = s • v)
    {n : ℕ} {b : Fin n → F} {m : Fin n → ℕ}
    (hcover : ∀ x ∈ π '' K, x ∈ L.map (π : E →+ F) → ∃ c ∈ intBox m, ∑ i, (c i : ℝ) • b i = x)
    {y : Fin n → E} (hyL : ∀ i, y i ∈ L) (hyb : ∀ i, π (y i) = b i) {B : ℝ}
    (hy : ∀ i, m i * gauge K (y i) ≤ B) {x : E} (hxK : x ∈ K) (hxL : x ∈ L) :
    ∃ k : ℤ, ∃ c ∈ intBox m, x = (k : ℝ) • v + ∑ i, (c i : ℝ) • y i ∧
      |(k : ℝ)| * gauge K v ≤ 1 + n * B := by
  obtain ⟨c, hc, hcx⟩ := hcover (π x) ⟨x, hxK, rfl⟩ (AddSubgroup.mem_map_of_mem _ hxL)
  obtain ⟨t, ht⟩ := hker (x - ∑ i, (c i : ℝ) • y i) (by simp [hyb, hcx])
  obtain ⟨k, hk⟩ := exists_intCast_smul_eq_of_gauge_min hconv hsymm hvL hvpos hmin
    (L.sub_mem hxL (AddSubgroup.sum_mem _ fun i _ ↦ by
      simpa [Int.cast_smul_eq_zsmul] using L.zsmul_mem (hyL i) (c i))) ht
  refine ⟨k, c, hc, sub_eq_iff_eq_add.mp hk, ?_⟩
  rw [← Real.norm_eq_abs, ← gauge_smul ((balanced_iff_neg_mem hconv).mpr hsymm), ← hk,
    sub_eq_add_neg]
  refine (gauge_add_le hconv (absorbent_nhds_zero hK₀) _ _).trans
    (add_le_add (gauge_le_one_of_mem hxK) ?_)
  rw [gauge_neg hsymm]
  exact gauge_sum_intCast_smul_le_mul hconv hK₀ hsymm hy hc

/-- The inductive step. Let `v ∈ L` be a nonzero vector of least gauge and let `π : E →ₗ[ℝ] F` be
a linear map with kernel `ℝ ∙ v`. Let `b : Fin n → F` be linearly independent vectors of
`L.map π` and `m : Fin n → ℕ` such that every point of `π '' K ∩ L.map π` is `∑ i, c i • b i`
with `c ∈ intBox m`, and `m i * gauge (π '' K) (b i) ≤ A`. Then `L` and `K` have `n + 1` such
vectors and half-widths with gauge bound `1 + 4 * n * A`. -/
lemma exists_linearIndependent_mem_intBox_gauge_le_of_map (hconv : Convex ℝ K) (hK₀ : K ∈ 𝓝 0)
    (hsymm : ∀ x ∈ K, -x ∈ K) {π : E →ₗ[ℝ] F} {v : E} (hvL : v ∈ L) (hv₀ : v ≠ 0)
    (hvpos : 0 < gauge K v) (hmin : ∀ y ∈ L, y ≠ 0 → gauge K v ≤ gauge K y) (hπv : π v = 0)
    (hker : ∀ x, π x = 0 → ∃ s : ℝ, x = s • v) (hKπ : IsCompact (π '' K))
    (hKπ₀ : π '' K ∈ 𝓝 0) {n : ℕ} {A : ℝ} (hA : 0 ≤ A) {b : Fin n → F} {m : Fin n → ℕ}
    (hbL : ∀ i, b i ∈ L.map (π : E →+ F)) (hb : LinearIndependent ℝ b)
    (hcover : ∀ x ∈ π '' K, x ∈ L.map (π : E →+ F) → ∃ c ∈ intBox m, ∑ i, (c i : ℝ) • b i = x)
    (hgauge : ∀ i, m i * gauge (π '' K) (b i) ≤ A) :
    ∃ (b' : Fin (n + 1) → E) (m' : Fin (n + 1) → ℕ), (∀ i, b' i ∈ L) ∧
      LinearIndependent ℝ b' ∧ (∀ x ∈ K, x ∈ L → ∃ c ∈ intBox m', ∑ i, (c i : ℝ) • b' i = x) ∧
      ∀ i, m' i * gauge K (b' i) ≤ 1 + 4 * n * A := by
  choose y hyL hyb hy using fun i ↦ exists_mem_apply_eq_gauge_le_two_mul hconv hK₀ hsymm hvL
    hπv hker hmin hKπ hKπ₀ (hbL i) (hb.ne_zero i)
  have hym (i : Fin n) : m i * gauge K (y i) ≤ 2 * A := by
    nlinarith [hgauge i, hy i, (m i).cast_nonneg (α := ℝ)]
  refine ⟨Fin.cons v y, Fin.cons ⌊(1 + n * (2 * A)) / gauge K v⌋₊ m, Fin.cases hvL hyL,
    linearIndependent_finCons_of_apply_eq_zero hv₀ hπv hyb hb, ?_, ?_⟩
  · intro x hxK hxL
    obtain ⟨k, c, hc, rfl, hk⟩ := exists_intCast_smul_add_sum_eq hconv hK₀ hsymm hvL hvpos
      hmin hker hcover hyL hyb hym hxK hxL
    refine ⟨Fin.cons k c, ?_, by simp [Fin.sum_univ_succ]⟩
    rw [mem_intBox]
    refine Fin.cases ?_ (mem_intBox.mp hc)
    simp only [Fin.cons_zero, Int.abs_eq_natAbs, Nat.cast_le]
    exact Nat.le_floor ((le_div_iff₀ hvpos).mpr (by simpa [Nat.cast_natAbs] using hk))
  · refine Fin.cases ?_ ?_
    · simp only [Fin.cons_zero]
      nlinarith [(le_div_iff₀ hvpos).mp (Nat.floor_le (by positivity) :
        (⌊(1 + n * (2 * A)) / gauge K v⌋₊ : ℝ) ≤ (1 + n * (2 * A)) / gauge K v),
        mul_nonneg (n.cast_nonneg (α := ℝ)) hA]
    · intro i
      simp only [Fin.cons_succ]
      nlinarith [hym i, (Nat.one_le_cast.mpr i.pos : (1 : ℝ) ≤ n)]

/-- If `E` has dimension `n`, `L` is a discrete subgroup of `E`, and `K` is a compact symmetric
convex neighborhood of `0` such that `K ∩ L` spans `E`, then there are linearly independent
`b : Fin n → E` in `L` and `m : Fin n → ℕ` such that every point of `K ∩ L` is `∑ i, c i • b i`
with `c ∈ intBox m`, and `m i * gauge K (b i) ≤ latticeBoxGaugeBound n`. -/
lemma exists_linearIndependent_mem_intBox_gauge_le {n : ℕ} {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {L : AddSubgroup E} [DiscreteTopology L]
    {K : Set E} (hrank : finrank ℝ E = n) (hconv : Convex ℝ K) (hcompact : IsCompact K)
    (hK₀ : K ∈ 𝓝 0) (hsymm : ∀ x ∈ K, -x ∈ K)
    (hspan : Submodule.span ℝ (K ∩ (L : Set E)) = ⊤) :
    ∃ (b : Fin n → E) (m : Fin n → ℕ), (∀ i, b i ∈ L) ∧ LinearIndependent ℝ b ∧
      (∀ x ∈ K, x ∈ L → ∃ c ∈ intBox m, ∑ i, (c i : ℝ) • b i = x) ∧
      ∀ i, m i * gauge K (b i) ≤ latticeBoxGaugeBound n := by
  induction n generalizing E with
  | zero =>
      have := finrank_zero_iff.mp hrank
      refine ⟨Fin.elim0, Fin.elim0, by simp, linearIndependent_empty_type, ?_, by simp⟩
      intro x _ _
      exact ⟨0, zero_mem_intBox _, Subsingleton.elim _ _⟩
  | succ n ih =>
      have := nontrivial_of_finrank_eq_succ hrank
      obtain ⟨v, hvL, hv₀, hvpos, hmin⟩ :=
        exists_mem_ne_zero_gauge_pos_forall_gauge_le hconv hcompact hK₀ hspan
      obtain ⟨W, hcompl⟩ := (ℝ ∙ v).exists_isCompl
      have := discreteTopology_map_projectionOnto hvL hcompl.symm
      set π := W.projectionOnto (ℝ ∙ v) hcompl.symm
      have hK₀' : π '' K ∈ 𝓝 0 := by
        simpa using (LinearMap.isOpenMap_of_finiteDimensional π
          (Submodule.projectionOnto_surjective hcompl.symm)).image_mem_nhds hK₀
      obtain ⟨b, m, hbL, hb, hcover, hgauge⟩ := ih (L := L.map (π : E →+ W)) (K := π '' K)
        (finrank_eq_of_isCompl_span_singleton hv₀ hcompl.symm hrank) (hconv.linear_image π)
        (hcompact.image π.continuous_of_finiteDimensional) hK₀' (neg_mem_image hsymm)
        (span_inter_image_map_eq_top (Submodule.projectionOnto_surjective _) hspan)
      simpa [latticeBoxGaugeBound] using exists_linearIndependent_mem_intBox_gauge_le_of_map hconv
        hK₀ hsymm
        (π := π) hvL hv₀ hvpos hmin (Submodule.projectionOnto_apply_of_mem_right _
          (Submodule.mem_span_singleton_self v))
        (fun x hx ↦ (Submodule.mem_span_singleton.mp
          ((Submodule.projectionOnto_apply_eq_zero_iff _).mp hx)).imp fun _ ↦ Eq.symm)
        (hcompact.image π.continuous_of_finiteDimensional) hK₀' (Nat.cast_nonneg _) hbL hb
        hcover hgauge

/-- Let `K ⊆ ℝ ^ s` be a compact symmetric convex neighborhood of `0` whose integer points span
`ℝ ^ s`, and let `D` be the set of integer points of `K`. Then `D` lies in a proper GAP of
dimension at most `s` with at most `latticeBoxFactor s` times as many elements. -/
lemma exists_proper_gap_of_convex_body {s : ℕ} {K : Set (Fin s → ℝ)} (hconv : Convex ℝ K)
    (hcompact : IsCompact K) (hK₀ : K ∈ 𝓝 0) (hsymm : ∀ x ∈ K, -x ∈ K)
    (hspan : Submodule.span ℝ (K ∩
      ((⊤ : AddSubgroup (Fin s → ℤ)).map intVectorToReal : Set (Fin s → ℝ))) = ⊤)
    {D : Finset (Fin s → ℤ)} (hD : ∀ v, v ∈ D ↔ intVectorToReal v ∈ K) :
    ∃ Q : GAP (Fin s → ℤ), Q.Proper ∧ D ⊆ Q.carrier ∧ Q.dim ≤ s ∧
      Q.carrier.card ≤ latticeBoxFactor s * D.card := by
  have := BoxLattice.discreteTopology_map (⊤ : AddSubgroup (Fin s → ℤ))
  obtain ⟨b, m, hbL, hb, hcover, hgauge⟩ :=
    exists_linearIndependent_mem_intBox_gauge_le (finrank_fin_fun ℝ) hconv hcompact hK₀ hsymm hspan
  exact exists_proper_gap_card_le_of_gauge_le hconv hcompact hK₀ hsymm hD hbL hb hcover hgauge

end

end ChangFreimanRuzsa
