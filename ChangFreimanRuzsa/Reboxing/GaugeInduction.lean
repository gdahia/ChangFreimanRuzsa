/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.Reboxing.GaugeBox
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Shortest-direction induction for adapted lattice boxes

This file is the recursive geometric core used by the box projection and box slice wrappers. The
quantitative invariant is the endpoint gauge bound packaged by `GaugeControlledLatticeBox`.

It is also the top of the `Chang.Reboxing` directory, the common geometric development for the two
shapes used in Chang's theorem:

* projections of coefficient boxes along saturated spaces of short relations;
* slices of coefficient boxes by the saturated rational span of translated coordinates.

`GaugeBox` turns the endpoint bounds proved here into a cardinality estimate, `AdaptedBox` packages
the resulting integral steps and widths as a proper GAP, and `EffectiveLattice` supplies the
saturated coordinates used by the slice wrapper. The applications are the concrete projected-box
and sliced-box theorems in `Chang.Properization` and `Chang.Transport`.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open scoped Pointwise Topology

open ConvexGeometry Metric Module

noncomputable section

universe u

/-- A full-rank discrete lattice in a symmetric convex body admits a gauge-controlled lattice
box. The deliberately loose recurrence is absorbed by the later cubic reboxing budget. -/
theorem exists_gaugeControlledLatticeBox_aux :
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
        have hbot : Submodule.span ℝ (K ∩ (L : Set E)) = ⊥ := by
          apply le_antisymm
          · refine Submodule.span_le.mpr ?_
            intro x hx
            change x = 0
            exact hcon x hx.1 hx.2
          · exact bot_le
        exact top_ne_bot (hspan.symm.trans hbot)
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
        omega
      have hπsurj : Function.Surjective π := by
        intro x
        exact ⟨x, Submodule.projectionOnto_apply_left hcompl x⟩
      have hπcont : Continuous π := LinearMap.continuous_of_finiteDimensional π
      have hKcompact : IsCompact K := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
      have hKbar₀ : π '' K ∈ 𝓝 (0 : W) := by
        have hpre : (fun x : W ↦ (x : E)) ⁻¹' K ∈ 𝓝 (0 : W) := by
          apply continuous_subtype_val.continuousAt.preimage_mem_nhds
          simpa using hK₀
        apply Filter.mem_of_superset hpre
        intro x hx
        exact ⟨(x : E), hx, Submodule.projectionOnto_apply_left hcompl x⟩
      have hpv : p v = 0 :=
        Submodule.projection_apply_of_mem_right hcompl
          (Submodule.mem_span_singleton_self v)
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
        obtain ⟨r, hrpos, hr⟩ :=
          exists_pos_forall_norm_apply_lt (L := L) p hvL hpv hsplit
        refine ⟨r, hrpos, ?_⟩
        rintro x hx hnorm
        obtain ⟨y, hyL, rfl⟩ := AddSubgroup.mem_map.mp hx
        exact Subtype.ext (hr y hyL hnorm)
      have hspanbar :
          Submodule.span ℝ
            ((π '' K) ∩ ((L.map (π : E →+ W)) : Set W)) = ⊤ :=
        span_inter_image_map_eq_top L K π hπsurj hspan
      let Bbar := Classical.choice <|
        ih (L.map (π : E →+ W)) (π '' K) hWrank
          (convex_image hconv π) (hKcompact.image hπcont).isClosed hKbar₀
          (hKcompact.image hπcont).isBounded (neg_mem_image hsymm π) hspanbar
      have hKbarVonN : Bornology.IsVonNBounded ℝ (π '' K) :=
        (NormedSpace.isVonNBounded_iff ℝ).mpr (hKcompact.image hπcont).isBounded
      choose y hyL hyπ hygauge using fun i ↦
        exists_mem_gauge_le_of_mem_map hconv hK₀ hsymm π hvL hπv hker
          (gauge_nonneg (Bbar.step i)) (Bbar.step_mem i)
          ((mem_smul_iff_gauge_le (convex_image hconv π)
            (hKcompact.image hπcont).isClosed hKbar₀ hKbarVonN
            (gauge_nonneg (Bbar.step i)) (Bbar.step i)).mpr le_rfl)
      have hyendpoint : ∀ i,
          (Bbar.halfWidth i : ℝ) * gauge K (y i) ≤
            2 * gaugeReboxingDilation m := by
        intro i
        have hzNe : Bbar.step i ≠ 0 := Bbar.step_independent.ne_zero i
        have hshort :
            ConvexGeometry.HasIndependentShort (L.map (π : E →+ W)) (π '' K) 1
              (gauge (π '' K) (Bbar.step i)) :=
          ⟨fun _ ↦ Bbar.step i, linearIndependent_unique_iff.mpr hzNe, fun _ ↦
            ⟨Bbar.step_mem i,
              (mem_smul_iff_gauge_le (convex_image hconv π)
                (hKcompact.image hπcont).isClosed hKbar₀ hKbarVonN
                (gauge_nonneg (Bbar.step i)) (Bbar.step i)).mpr le_rfl⟩⟩
        have hlower : gauge K v ≤ 2 * gauge (π '' K) (Bbar.step i) :=
          gauge_le_two_mul_of_mem_map hconv hK₀ hsymm π hvL hπv hker hmin
            (gauge_nonneg (Bbar.step i)) hshort
        exact endpoint_gauge_lift_le_two_mul (hygauge i) hlower
          (Bbar.endpoint_gauge i)
      have hyindep : LinearIndependent ℝ y := by
        apply LinearIndependent.of_comp π
        have hcomp : (π : E → W) ∘ y = Bbar.step := funext hyπ
        rw [hcomp]
        exact Bbar.step_independent
      have hvnotspan : v ∉ Submodule.span ℝ (Set.range y) := by
        intro hvspan
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hvspan
        have hczero : ∑ i, c i • Bbar.step i = 0 := by
          rw [← hπv, ← hc, map_sum]
          exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, hyπ]
        apply hvne
        rw [← hc, Finset.sum_eq_zero fun i _ ↦ ?_]
        rw [Fintype.linearIndependent_iff.mp Bbar.step_independent c hczero i,
          zero_smul]
      have hfinite : (K ∩ (L : Set E)).Finite :=
        Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete hbdd
          AddSubgroup.isClosed_of_discreteTopology
      let S := hfinite.toFinset
      have hrepr : ∀ x : E, ∃ c ∈ intBox Bbar.halfWidth, ∃ k : ℤ,
          x ∈ K ∧ x ∈ L →
            x = (k : ℝ) • v + ∑ i, (c i : ℝ) • y i := by
        intro x
        by_cases hx : x ∈ K ∧ x ∈ L
        · obtain ⟨c, hc, hcπ⟩ :=
            Bbar.cover (π x) ⟨x, hx.1, rfl⟩
              (AddSubgroup.mem_map.mpr ⟨x, hx.2, rfl⟩)
          have hresker : π (x - ∑ i, (c i : ℝ) • y i) = 0 := by
            rw [map_sub, map_sum]
            simp_rw [map_smul, hyπ]
            rw [hcπ, sub_self]
          obtain ⟨t, ht⟩ := hker _ hresker
          have hresL : x - ∑ i, (c i : ℝ) • y i ∈ L := by
            apply L.sub_mem hx.2
            simp_rw [Int.cast_smul_eq_zsmul]
            exact AddSubgroup.sum_mem L fun i _ ↦ L.zsmul_mem (hyL i) (c i)
          obtain ⟨k, hk⟩ :=
            exists_intCast_smul_eq_of_gauge_min hsymm hvL hvpos hmin hresL ht
          refine ⟨c, hc, k, ?_⟩
          intro _
          rw [← hk]
          abel
        · exact ⟨0, zero_mem_intBox _, 0, fun h ↦ absurd h hx⟩
      choose c hc k hk using hrepr
      let m₀ := S.sup fun x ↦ (k x).natAbs
      have hzeroS : (0 : E) ∈ S := by
        change (0 : E) ∈ hfinite.toFinset
        rw [Set.Finite.mem_toFinset]
        exact ⟨mem_of_mem_nhds hK₀, L.zero_mem⟩
      have hm₀ : (m₀ : ℝ) * gauge K v ≤
          1 + (m : ℝ) * (2 * gaugeReboxingDilation m) := by
        obtain ⟨x, hxS, hxsup⟩ :=
          Finset.exists_mem_eq_sup S ⟨0, hzeroS⟩ fun z ↦ (k z).natAbs
        have hxmem : x ∈ K ∧ x ∈ L := by
          change x ∈ hfinite.toFinset at hxS
          rw [Set.Finite.mem_toFinset] at hxS
          exact hxS
        have hxgauge : gauge K x ≤ 1 := gauge_le_one_of_mem hxmem.1
        have hsumgauge :
            gauge K (∑ i, (c x i : ℝ) • y i) ≤
              (m : ℝ) * (2 * gaugeReboxingDilation m) :=
          gauge_sum_zsmul_le_card_mul hconv hK₀ hsymm y Bbar.halfWidth
            hyendpoint (hc x)
        have hresgauge :
            gauge K ((k x : ℝ) • v) ≤
              1 + (m : ℝ) * (2 * gaugeReboxingDilation m) := by
          have heq :
              (k x : ℝ) • v = x - ∑ i, (c x i : ℝ) • y i := by
            exact eq_sub_iff_add_eq.mpr (hk x hxmem).symm
          rw [heq, sub_eq_add_neg]
          apply (gauge_add_le hconv (absorbent_nhds_zero hK₀) x
            (-∑ i, (c x i : ℝ) • y i)).trans
          rw [gauge_neg hsymm]
          exact add_le_add hxgauge hsumgauge
        rw [gauge_smul_abs hsymm] at hresgauge
        have hkabs : |(k x : ℝ)| = ((k x).natAbs : ℝ) := by
          rw [← Int.cast_abs, Int.abs_eq_natAbs]
          norm_num
        dsimp only [m₀]
        rw [hxsup]
        simpa only [hkabs] using hresgauge
      let step : Fin (m + 1) → E := Fin.cons v y
      let halfWidth : Fin (m + 1) → ℕ := Fin.cons m₀ Bbar.halfWidth
      refine ⟨{
        step := step
        halfWidth := halfWidth
        step_mem := by
          refine Fin.cases hvL ?_
          intro i
          exact hyL i
        step_independent := linearIndependent_finCons.mpr ⟨hyindep, hvnotspan⟩
        cover := by
          intro x hxK hxL
          let coeff : Fin (m + 1) → ℤ := Fin.cons (k x) (c x)
          refine ⟨coeff, ?_, ?_⟩
          · rw [mem_intBox]
            apply Fin.cases
            · change |k x| ≤ (m₀ : ℤ)
              rw [Int.abs_eq_natAbs]
              have hxS : x ∈ S := by
                change x ∈ hfinite.toFinset
                rw [Set.Finite.mem_toFinset]
                exact ⟨hxK, hxL⟩
              exact_mod_cast Finset.le_sup (f := fun z ↦ (k z).natAbs)
                hxS
            · intro i
              exact mem_intBox.mp (hc x) i
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
            have hmnonneg : (0 : ℝ) ≤ m := Nat.cast_nonneg m
            have hAnonneg : (0 : ℝ) ≤ gaugeReboxingDilation m :=
              Nat.cast_nonneg _
            nlinarith [mul_nonneg hmnonneg hAnonneg]
          · intro i
            change (Bbar.halfWidth i : ℝ) * gauge K (y i) ≤
              (gaugeReboxingDilation (m + 1) : ℝ)
            rw [gaugeReboxingDilation]
            push_cast
            have hmpos : 0 < m :=
              lt_of_le_of_lt (Nat.zero_le i) i.isLt
            have hApos := gaugeReboxingDilation_pos hmpos
            have hAposR : (0 : ℝ) < gaugeReboxingDilation m := by
              exact_mod_cast hApos
            apply (hyendpoint i).trans
            have hmoneR : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
            have hAm :
                (gaugeReboxingDilation m : ℝ) ≤
                  m * gaugeReboxingDilation m :=
              by simpa only [one_mul] using
                mul_le_mul_of_nonneg_right hmoneR hAposR.le
            nlinarith
      }⟩

end

end ChangFreimanRuzsa
