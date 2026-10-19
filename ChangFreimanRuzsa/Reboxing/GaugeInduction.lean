/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.Reboxing.GaugeBox
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Shortest-vector induction for gauge-controlled lattice boxes

Let $E$ be a real normed space of dimension $n$, let $L \subseteq E$ be a discrete subgroup, and
let $K \subseteq E$ be a closed bounded symmetric convex neighbourhood of $0$ such that $K \cap L$
spans $E$. Then there is a `GaugeControlledLatticeBox L K n A_n`, where $A_n$ is
`gaugeReboxingDilation n`.

The proof is by induction on $n$. Choose a nonzero $v \in L$ of minimal gauge and project $E$
onto a complement $W$ of $\mathbb{R} v$. The induction hypothesis gives a box for the projections
of $L$ and $K$ in $W$. Each of its steps lifts to a step in $L$ whose gauge is at most the gauge
of the projected step plus half the gauge of $v$, and $v$ is added as a new step whose half-width
covers the multiples of $v$ that remain.

The lemma is applied in `ChangFreimanRuzsa.Properization.AlgebraAndGAPBasics` and
`ChangFreimanRuzsa.CoordinateReduction`.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open scoped Pointwise Topology

open ConvexGeometry Metric Module

noncomputable section

universe u

/-- If $E$ has dimension $n$, $L$ is a discrete subgroup of $E$, and $K$ is a closed bounded
symmetric convex neighbourhood of $0$ such that $K \cap L$ spans $E$, then $L$ and $K$ have a
gauge-controlled lattice box of rank $n$ with gauge bound `gaugeReboxingDilation n`. -/
lemma exists_gaugeControlledLatticeBox_aux :
    ∀ (n : ℕ) {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] (L : AddSubgroup E) [DiscreteTopology L] (K : Set E),
      finrank ℝ E = n →
      Convex ℝ K → IsClosed K → K ∈ 𝓝 0 → Bornology.IsBounded K →
      (∀ x ∈ K, -x ∈ K) →
      Submodule.span ℝ (K ∩ (L : Set E)) = ⊤ →
      Nonempty (GaugeControlledLatticeBox L K n (gaugeReboxingDilation n : ℝ)) := by
  intro n
  induction n with
  | zero =>
      intro E _ _ _ L _ K hrank _ _ _ _ _ _
      constructor
      simpa [gaugeReboxingDilation] using gaugeControlledLatticeBoxZero L K hrank
  | succ m ih =>
      intro E _ _ _ L _ K hrank hconv hclosed hK₀ hbdd hsymm hspan
      have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hrank
      have hex : ∃ x, x ∈ K ∧ x ∈ L ∧ x ≠ 0 := by
        by_contra! hcon
        apply top_ne_bot (α := Submodule ℝ E)
        rw [← hspan, Submodule.span_eq_bot]
        rintro x ⟨hxK, hxL⟩
        exact hcon x hxK hxL
      obtain ⟨v, hvL, hvne, hvpos, hmin⟩ :=
        exists_shortest_lattice_direction L K hconv hclosed hK₀ hbdd hex
      obtain ⟨W, hWcompl⟩ := (Submodule.span ℝ {v}).exists_isCompl
      have hcompl : IsCompl W (Submodule.span ℝ {v}) := hWcompl.symm
      let π : E →ₗ[ℝ] W :=
        Submodule.projectionOnto W (Submodule.span ℝ {v}) hcompl
      let p : E →ₗ[ℝ] E :=
        Submodule.projection W (Submodule.span ℝ {v}) hcompl
      have hπv : π v = 0 :=
        Submodule.projectionOnto_apply_of_mem_right hcompl
          (Submodule.mem_span_singleton_self v)
      have hker : ∀ x : E, π x = 0 → ∃ s : ℝ, x = s • v := by
        intro x hx
        have hxspan : x ∈ Submodule.span ℝ {v} := by
          rw [← Submodule.ker_projectionOnto hcompl]
          exact LinearMap.mem_ker.mpr hx
        obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hxspan
        exact ⟨s, hs.symm⟩
      have hWrank : finrank ℝ W = m := by
        have hsum := Submodule.finrank_add_eq_of_isCompl hWcompl
        rw [finrank_span_singleton hvne, hrank] at hsum
        grind
      have hπsurj : Function.Surjective π := by
        intro x
        exact ⟨x, Submodule.projectionOnto_apply_left hcompl x⟩
      have hπcont : Continuous π := LinearMap.continuous_of_finiteDimensional π
      have hKcompact : IsCompact K := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
      have hKbar₀ : π '' K ∈ 𝓝 (0 : W) := by
        refine Filter.mem_of_superset
          (continuous_subtype_val.continuousAt.preimage_mem_nhds (by simpa using hK₀)) ?_
        intro x hx
        exact ⟨(x : E), hx, Submodule.projectionOnto_apply_left hcompl x⟩
      have hsplit : ∀ y : E, ∃ s : ℝ, y - p y = s • v := by
        intro y
        have hmem : y - p y ∈ Submodule.span ℝ {v} := by
          rw [← Submodule.ker_projection hcompl]
          apply LinearMap.mem_ker.mpr
          rw [map_sub, Submodule.projection_apply_of_mem_left hcompl
            (Submodule.projection_apply_mem hcompl y), sub_self]
        obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hmem
        exact ⟨s, hs.symm⟩
      have : DiscreteTopology (L.map (π : E →+ W)) := by
        apply discreteTopology_of_exists_pos_forall_norm_lt
        obtain ⟨r, hrpos, hr⟩ := exists_pos_forall_norm_apply_lt (L := L) p hvL
          (Submodule.projection_apply_of_mem_right hcompl (Submodule.mem_span_singleton_self v))
          hsplit
        refine ⟨r, hrpos, ?_⟩
        rintro x hx hnorm
        obtain ⟨y, hyL, rfl⟩ := AddSubgroup.mem_map.mp hx
        exact Subtype.ext (hr y hyL hnorm)
      obtain ⟨Bbar⟩ := ih (L.map (π : E →+ W)) (π '' K) hWrank
        (convex_image hconv π) (hKcompact.image hπcont).isClosed hKbar₀
        (hKcompact.image hπcont).isBounded (neg_mem_image hsymm π)
        (span_inter_image_map_eq_top L K π hπsurj hspan)
      have hstepmem : ∀ i, Bbar.step i ∈ gauge (π '' K) (Bbar.step i) • (π '' K) := by
        intro i
        exact (mem_smul_iff_gauge_le (convex_image hconv π) (hKcompact.image hπcont).isClosed
          hKbar₀ ((NormedSpace.isVonNBounded_iff ℝ).mpr (hKcompact.image hπcont).isBounded)
          (gauge_nonneg (Bbar.step i)) (Bbar.step i)).mpr le_rfl
      choose y hyL hyπ hygauge using fun i ↦
        exists_mem_gauge_le_of_mem_map hconv hK₀ hsymm π hvL hπv hker
          (gauge_nonneg (Bbar.step i)) (Bbar.step_mem i) (hstepmem i)
      have hyendpoint : ∀ i,
          (Bbar.halfWidth i : ℝ) * gauge K (y i) ≤ 2 * gaugeReboxingDilation m := by
        intro i
        refine endpoint_gauge_lift_le_two_mul (hygauge i) ?_ (Bbar.endpoint_gauge i)
        apply gauge_le_two_mul_of_mem_map hconv hK₀ hsymm π hvL hπv hker hmin
          (gauge_nonneg (Bbar.step i))
        exact ⟨fun _ ↦ Bbar.step i, linearIndependent_unique_iff.mpr
          (Bbar.step_independent.ne_zero i), fun _ ↦ ⟨Bbar.step_mem i, hstepmem i⟩⟩
      have hyindep : LinearIndependent ℝ y := by
        apply LinearIndependent.of_comp π
        convert Bbar.step_independent
        exact funext hyπ
      have hvnotspan : v ∉ Submodule.span ℝ (Set.range y) := by
        intro hvspan
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hvspan
        have hczero : ∑ i, c i • Bbar.step i = 0 := by
          rw [← hπv, ← hc, map_sum]
          simp [hyπ]
        apply hvne
        rw [← hc]
        simp [Fintype.linearIndependent_iff.mp Bbar.step_independent c hczero]
      have hfinite : (K ∩ (L : Set E)).Finite :=
        Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete hbdd
          AddSubgroup.isClosed_of_discreteTopology
      let S := hfinite.toFinset
      have hrepr : ∀ x : E, ∃ c ∈ intBox Bbar.halfWidth, ∃ k : ℤ,
          x ∈ K ∧ x ∈ L →
            x = (k : ℝ) • v + ∑ i, (c i : ℝ) • y i := by
        intro x
        by_cases hx : x ∈ K ∧ x ∈ L
        swap
        · exact ⟨0, zero_mem_intBox _, 0, fun h ↦ absurd h hx⟩
        obtain ⟨hxK, hxL⟩ := hx
        obtain ⟨c, hc, hcπ⟩ := Bbar.cover (π x) ⟨x, hxK, rfl⟩ (AddSubgroup.mem_map_of_mem _ hxL)
        have hresker : π (x - ∑ i, (c i : ℝ) • y i) = 0 := by
          rw [map_sub, map_sum]
          simp_rw [map_smul, hyπ]
          rw [hcπ, sub_self]
        obtain ⟨t, ht⟩ := hker _ hresker
        have hresL : x - ∑ i, (c i : ℝ) • y i ∈ L := by
          apply L.sub_mem hxL
          simp_rw [Int.cast_smul_eq_zsmul]
          apply AddSubgroup.sum_mem
          intro i _
          exact L.zsmul_mem (hyL i) (c i)
        obtain ⟨k, hk⟩ := exists_intCast_smul_eq_of_gauge_min hsymm hvL hvpos hmin hresL ht
        refine ⟨c, hc, k, ?_⟩
        intro _
        rw [← hk]
        abel
      choose c hc k hk using hrepr
      let m₀ := S.sup fun x ↦ (k x).natAbs
      have hm₀ : (m₀ : ℝ) * gauge K v ≤ 1 + (m : ℝ) * (2 * gaugeReboxingDilation m) := by
        obtain ⟨x, hxS, hxsup⟩ := Finset.exists_mem_eq_sup S
          ⟨0, hfinite.mem_toFinset.mpr ⟨mem_of_mem_nhds hK₀, L.zero_mem⟩⟩ fun z ↦ (k z).natAbs
        obtain ⟨hxK, hxL⟩ := hfinite.mem_toFinset.mp hxS
        have hresgauge :
            gauge K ((k x : ℝ) • v) ≤ 1 + (m : ℝ) * (2 * gaugeReboxingDilation m) := by
          rw [eq_sub_iff_add_eq.mpr (hk x ⟨hxK, hxL⟩).symm, sub_eq_add_neg]
          apply (gauge_add_le hconv (absorbent_nhds_zero hK₀) _ _).trans
          rw [gauge_neg hsymm]
          exact add_le_add (gauge_le_one_of_mem hxK)
            (gauge_sum_zsmul_le_card_mul hconv hK₀ hsymm y Bbar.halfWidth hyendpoint (hc x))
        rw [gauge_smul_abs hsymm] at hresgauge
        dsimp only [m₀]
        rw [hxsup]
        simpa [Nat.cast_natAbs] using hresgauge
      let step : Fin (m + 1) → E := Fin.cons v y
      let halfWidth : Fin (m + 1) → ℕ := Fin.cons m₀ Bbar.halfWidth
      refine ⟨{
        step := step
        halfWidth := halfWidth
        step_mem := Fin.cases hvL hyL
        step_independent := linearIndependent_finCons.mpr ⟨hyindep, hvnotspan⟩
        cover := by
          intro x hxK hxL
          refine ⟨Fin.cons (k x) (c x), ?_, ?_⟩
          · rw [mem_intBox]
            apply Fin.cases
            · change |k x| ≤ (m₀ : ℤ)
              rw [Int.abs_eq_natAbs]
              exact_mod_cast Finset.le_sup (f := fun z ↦ (k z).natAbs)
                (hfinite.mem_toFinset.mpr ⟨hxK, hxL⟩)
            · exact mem_intBox.mp (hc x)
          · rw [Fin.sum_univ_succ]
            change (k x : ℝ) • v + ∑ i, (c x i : ℝ) • y i = x
            exact (hk x ⟨hxK, hxL⟩).symm
        endpoint_gauge := by
          apply Fin.cases
          · change (m₀ : ℝ) * gauge K v ≤
              (gaugeReboxingDilation (m + 1) : ℝ)
            rw [gaugeReboxingDilation]
            push_cast
            apply hm₀.trans
            linarith [(by positivity : (0 : ℝ) ≤ m * gaugeReboxingDilation m)]
          · intro i
            change (Bbar.halfWidth i : ℝ) * gauge K (y i) ≤
              (gaugeReboxingDilation (m + 1) : ℝ)
            rw [gaugeReboxingDilation]
            push_cast
            apply (hyendpoint i).trans
            nlinarith [(Nat.one_le_cast.mpr i.pos : (1 : ℝ) ≤ m),
              (Nat.cast_nonneg _ : (0 : ℝ) ≤ gaugeReboxingDilation m)]
      }⟩

end

end ChangFreimanRuzsa
