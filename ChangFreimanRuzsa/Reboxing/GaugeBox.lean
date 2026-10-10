/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.BoxLatticePoints
public import ChangFreimanRuzsa.Reboxing.AdaptedBox
public import ChangFreimanRuzsa.ConvexProgression
import ChangFreimanRuzsa.Lattice
import ChangFreimanRuzsa.Reboxing.ConvexCardinality

/-! # Gauge bounds for lattice coefficient boxes

The projection induction constructs independent lattice steps one rank at a time. Its quantitative
invariant is most naturally stated on the endpoints: if `mᵢ bᵢ` has controlled gauge for every
step, then the entire centered coefficient box has controlled gauge, with only a factor equal to
the number of steps.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open scoped Pointwise Topology

open ConvexGeometry Metric

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : ℕ} {K : Set E}

/-- Independent lattice steps whose coordinate endpoints have controlled gauge and whose centered
coefficient box contains all lattice points of the body. -/
structure GaugeControlledLatticeBox (L : AddSubgroup E) (K : Set E) (s : ℕ) (A : ℝ) where
  step : Fin s → E
  halfWidth : Fin s → ℕ
  step_mem : ∀ i, step i ∈ L
  step_independent : LinearIndependent ℝ step
  cover : ∀ x, x ∈ K → x ∈ L →
    ∃ c ∈ intBox halfWidth, ∑ i, (c i : ℝ) • step i = x
  endpoint_gauge : ∀ i, (halfWidth i : ℝ) * gauge K (step i) ≤ A

/-- A loose integral dilation budget for the shortest-vector projection induction. -/
def gaugeReboxingDilation : ℕ → ℕ
  | 0 => 0
  | s + 1 => 1 + 4 * s * gaugeReboxingDilation s

/-- The cardinality loss delivered by the gauge-controlled coefficient box in rank `s`. -/
def boxReboxingFactor (s : ℕ) : ℕ :=
  (2 * (s * gaugeReboxingDilation s) + 1) ^ s

lemma gaugeReboxingDilation_pos {s : ℕ} (hs : 0 < s) :
    0 < gaugeReboxingDilation s := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  simp [gaugeReboxingDilation]

lemma gaugeReboxingDilation_le_pow (s : ℕ) :
    gaugeReboxingDilation s ≤ (4 * s + 1) ^ s := by
  induction s with
  | zero => simp [gaugeReboxingDilation]
  | succ s ih =>
      rw [gaugeReboxingDilation]
      have hbase : 4 * s + 1 ≤ 4 * (s + 1) + 1 := by omega
      have hpow := Nat.pow_le_pow_left hbase s
      have hmul := Nat.mul_le_mul_left (4 * s) (ih.trans hpow)
      apply (Nat.add_le_add_left hmul 1).trans
      rw [pow_succ]
      have hone : 1 ≤ (4 * (s + 1) + 1) ^ s :=
        one_le_pow₀ (by omega)
      nlinarith

lemma boxReboxingFactor_le_pow (s : ℕ) :
    boxReboxingFactor s ≤ (4 * s + 1) ^ ((s + 2) * s) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp [boxReboxingFactor]
  have hA := gaugeReboxingDilation_le_pow s
  have hone : 1 ≤ (4 * s + 1) ^ s := one_le_pow₀ (by omega)
  have hbase :
      2 * (s * gaugeReboxingDilation s) + 1 ≤ (4 * s + 1) ^ (s + 2) := by
    rw [pow_add]
    have hscaled := Nat.mul_le_mul_left (2 * s) hA
    have hfirst :
        2 * (s * gaugeReboxingDilation s) + 1 ≤
          (2 * s + 1) * (4 * s + 1) ^ s := by
      nlinarith
    apply hfirst.trans
    have hcoef : 2 * s + 1 ≤ (4 * s + 1) ^ 2 := by nlinarith
    simpa only [mul_comm] using
      Nat.mul_le_mul_right ((4 * s + 1) ^ s) hcoef
  unfold boxReboxingFactor
  apply (Nat.pow_le_pow_left hbase s).trans_eq
  rw [← pow_mul]

/-- The zero-rank base of the projection induction. -/
def gaugeControlledLatticeBoxZero
    [FiniteDimensional ℝ E] (L : AddSubgroup E) (K : Set E)
    (hrank : Module.finrank ℝ E = 0) :
    GaugeControlledLatticeBox L K 0 0 := by
  haveI : Subsingleton E := Module.finrank_zero_iff.mp hrank
  exact {
    step := Fin.elim0
    halfWidth := Fin.elim0
    step_mem := fun i ↦ Fin.elim0 i
    step_independent := linearIndependent_empty_type
    cover := fun x _ _ ↦ ⟨0, zero_mem_intBox _, by
      simpa using (Subsingleton.elim (0 : E) x)⟩
    endpoint_gauge := fun i ↦ Fin.elim0 i
  }

/-- Projecting a body and its lattice along a surjective linear map preserves full spanning by
lattice points. -/
lemma span_inter_image_map_eq_top
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : AddSubgroup E) (K : Set E) (π : E →ₗ[ℝ] F)
    (hπ : Function.Surjective π)
    (hspan : Submodule.span ℝ (K ∩ (L : Set E)) = ⊤) :
    Submodule.span ℝ
      ((π '' K) ∩ ((L.map (π : E →+ F)) : Set F)) = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := hπ y
  have hx : x ∈ Submodule.span ℝ (K ∩ (L : Set E)) := by
    rw [hspan]
    exact Submodule.mem_top
  have hmap :
      π x ∈ Submodule.map π (Submodule.span ℝ (K ∩ (L : Set E))) :=
    Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  rw [Submodule.map_span] at hmap
  refine Submodule.span_mono ?_ hmap
  rintro z ⟨x, hx, rfl⟩
  exact ⟨⟨x, hx.1, rfl⟩, AddSubgroup.mem_map.mpr ⟨x, hx.2, rfl⟩⟩

/-- Choose a shortest nonzero lattice direction meeting the body. -/
lemma exists_shortest_lattice_direction
    [FiniteDimensional ℝ E] (L : AddSubgroup E) [DiscreteTopology L] (K : Set E)
    (hconv : Convex ℝ K) (hclosed : IsClosed K) (hK₀ : K ∈ 𝓝 0)
    (hbdd : Bornology.IsBounded K)
    (hex : ∃ x, x ∈ K ∧ x ∈ L ∧ x ≠ 0) :
    ∃ v : E, v ∈ L ∧ v ≠ 0 ∧ 0 < gauge K v ∧
      ∀ y ∈ L, y ≠ 0 → gauge K v ≤ gauge K y := by
  have hvonN : Bornology.IsVonNBounded ℝ K :=
    (NormedSpace.isVonNBounded_iff ℝ).mpr hbdd
  obtain ⟨v₀, hv₀K, hv₀L, hv₀ne⟩ := hex
  have hne1 : ∃ t : ℝ, 0 ≤ t ∧ ConvexGeometry.HasIndependentShort L K 1 t :=
    ⟨1, zero_le_one, fun _ ↦ v₀, linearIndependent_unique_iff.mpr hv₀ne, fun _ ↦
      ⟨hv₀L, (mem_smul_iff_gauge_le hconv hclosed hK₀ hvonN zero_le_one v₀).mpr
        (gauge_le_one_of_mem hv₀K)⟩⟩
  obtain ⟨w, hwindep, hw⟩ :=
    ConvexGeometry.exists_witness_successiveMinimum
      (k := 1) (L := L) hconv hclosed hK₀ hbdd hne1
  let v := w 0
  have hvL : v ∈ L := (hw 0).1
  have hvne : v ≠ 0 := hwindep.ne_zero 0
  have hgaugele : gauge K v ≤ ConvexGeometry.successiveMinimum L K 1 :=
    (mem_smul_iff_gauge_le hconv hclosed hK₀ hvonN
      (ConvexGeometry.successiveMinimum_nonneg L K 1) v).mp (hw 0).2
  have hfirst : ∀ y ∈ L, y ≠ 0 →
      ConvexGeometry.successiveMinimum L K 1 ≤ gauge K y :=
    fun y hy hyne ↦
      ConvexGeometry.successiveMinimum_le (gauge_nonneg y)
        ⟨fun _ ↦ y, linearIndependent_unique_iff.mpr hyne,
          fun _ ↦ ⟨hy, (mem_smul_iff_gauge_le hconv hclosed hK₀ hvonN
            (gauge_nonneg y) y).mpr le_rfl⟩⟩
  have hlampos : 0 < ConvexGeometry.successiveMinimum L K 1 := by
    obtain ⟨R, hR⟩ := hbdd.subset_closedBall (0 : E)
    obtain ⟨r, hrpos, hr⟩ := exists_pos_forall_norm_lt L
    have hmaxpos : (0 : ℝ) < max R 1 :=
      lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hxpos : 0 < r / (2 * max R 1) := div_pos hrpos (by positivity)
    refine lt_of_lt_of_le hxpos (ConvexGeometry.le_successiveMinimum_one
      (hR.trans (closedBall_subset_closedBall (le_max_left R 1))) hr hxpos.le ?_ hne1)
    nlinarith [div_mul_cancel₀ r (by positivity : (2 * max R 1 : ℝ) ≠ 0),
      mul_pos hxpos hmaxpos]
  refine ⟨v, hvL, hvne, lt_of_lt_of_le hlampos (hfirst v hvL hvne), ?_⟩
  exact fun y hy hyne ↦ hgaugele.trans (hfirst y hy hyne)

/-- Endpoint gauge bounds control every linear combination in the centered integer box. -/
lemma gauge_sum_zsmul_le_card_mul
    (hconv : Convex ℝ K) (hK₀ : K ∈ 𝓝 0) (hsymm : ∀ x ∈ K, -x ∈ K)
    (step : Fin s → E) (m : Fin s → ℕ) {A : ℝ}
    (hend : ∀ i, (m i : ℝ) * gauge K (step i) ≤ A)
    {c : Fin s → ℤ} (hc : c ∈ intBox m) :
    gauge K (∑ i, (c i : ℝ) • step i) ≤ s * A := by
  apply (gauge_sum_le hconv (absorbent_nhds_zero hK₀) Finset.univ
    fun i ↦ (c i : ℝ) • step i).trans
  have hterm : ∀ i : Fin s, gauge K ((c i : ℝ) • step i) ≤ A := by
    intro i
    rw [gauge_smul_abs hsymm]
    refine (mul_le_mul_of_nonneg_right ?_ (gauge_nonneg (step i))).trans (hend i)
    have hi := mem_intBox.mp hc i
    exact_mod_cast hi
  apply (Finset.sum_le_sum fun i _ ↦ hterm i).trans_eq
  simp

lemma GaugeControlledLatticeBox.gauge_sum_le
    {L : AddSubgroup E} {A : ℝ} (B : GaugeControlledLatticeBox L K s A)
    (hconv : Convex ℝ K) (hK₀ : K ∈ 𝓝 0) (hsymm : ∀ x ∈ K, -x ∈ K)
    {c : Fin s → ℤ} (hc : c ∈ intBox B.halfWidth) :
    gauge K (∑ i, (c i : ℝ) • B.step i) ≤ s * A :=
  gauge_sum_zsmul_le_card_mul hconv hK₀ hsymm B.step B.halfWidth
    B.endpoint_gauge hc

lemma GaugeControlledLatticeBox.sum_injective
    {L : AddSubgroup E} {A : ℝ} (B : GaugeControlledLatticeBox L K s A) :
    Function.Injective (fun c : Fin s → ℤ ↦ ∑ i, (c i : ℝ) • B.step i) := by
  intro c c' h
  funext i
  have hzero :
      ∑ j, ((c j - c' j : ℤ) : ℝ) • B.step j = 0 := by
    simp only [Int.cast_sub, sub_smul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr h
  have hi := Fintype.linearIndependent_iff.mp B.step_independent
    (fun j ↦ ((c j - c' j : ℤ) : ℝ)) hzero i
  exact sub_eq_zero.mp (by exact_mod_cast hi)

/-- The endpoint estimate used when a projected step is lifted and reduced modulo the shortest
lattice direction. -/
lemma endpoint_gauge_lift_le_two_mul {m : ℕ} {A lam μ ν : ℝ}
    (hν : ν ≤ μ + lam / 2) (hlam : lam ≤ 2 * μ)
    (hend : (m : ℝ) * μ ≤ A) :
    (m : ℝ) * ν ≤ 2 * A := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

lemma intVectorToReal_stepsHom (step : Fin s → (Fin s → ℤ)) (c : Fin s → ℤ) :
    intVectorToReal (stepsHom step c) =
      ∑ i, (c i : ℝ) • intVectorToReal (step i) := by
  change intVectorToReal (∑ i, c i • step i) = _
  rw [intVectorToReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [intVectorToReal_zsmul, Int.cast_smul_eq_zsmul]

/-- A gauge-controlled box in the standard integer lattice gives an adapted integral box. Its
coordinate-box cardinality is bounded by the residue estimate applied to a dimension-only
dilate. -/
theorem GaugeControlledLatticeBox.exists_adaptedLatticeBox
    {D : Finset (Fin s → ℤ)} {K : Set (Fin s → ℝ)}
    (hconv : Convex ℝ K) (hclosed : IsClosed K) (hK₀ : K ∈ 𝓝 0)
    (hbdd : Bornology.IsVonNBounded ℝ K) (hsymm : ∀ x, x ∈ K ↔ -x ∈ K)
    (hDK : ∀ v : Fin s → ℤ, v ∈ D ↔ intVectorToReal v ∈ K)
    (a : ℕ)
    (B : GaugeControlledLatticeBox
      ((⊤ : AddSubgroup (Fin s → ℤ)).map
        (BoxLattice.intCastHom : (Fin s → ℤ) →+ (Fin s → ℝ)))
      K s (a : ℝ)) :
    ∃ C : AdaptedLatticeBox D,
      ∏ i, (2 * C.halfWidth i + 1) ≤ (2 * (s * a) + 1) ^ s * D.card := by
  choose stepZ hstepZ hstep using fun i ↦ AddSubgroup.mem_map.mp (B.step_mem i)
  have hstepReal : ∀ i, intVectorToReal (stepZ i) = B.step i := by
    intro i
    funext j
    exact congr_fun (hstep i) j
  let C : AdaptedLatticeBox D := {
    step := stepZ
    halfWidth := B.halfWidth
    stepHom_injective := by
      intro c c' hcc'
      apply B.sum_injective
      have hreal := congr_arg intVectorToReal hcc'
      rw [intVectorToReal_stepsHom, intVectorToReal_stepsHom] at hreal
      simpa only [hstepReal] using hreal
    mem_stepBox := by
      intro x hx
      have hxL :
          intVectorToReal x ∈
            (⊤ : AddSubgroup (Fin s → ℤ)).map
              (BoxLattice.intCastHom : (Fin s → ℤ) →+ (Fin s → ℝ)) := by
        exact AddSubgroup.mem_map.mpr ⟨x, by simp, rfl⟩
      obtain ⟨c, hc, hcx⟩ := B.cover (intVectorToReal x) ((hDK x).mp hx) hxL
      refine ⟨c, hc, intVectorToReal_injective ?_⟩
      rw [intVectorToReal_stepsHom]
      simp_rw [hstepReal]
      exact hcx
  }
  let T := (intBox C.halfWidth).image (stepsHom C.step)
  have hTcard : T.card = ∏ i, (2 * C.halfWidth i + 1) := by
    dsimp only [T]
    rw [Finset.card_image_of_injective _ C.stepHom_injective, card_intBox]
  have hTmem : ∀ v ∈ T,
      intVectorToReal v ∈ ((s * a : ℕ) : ℝ) • K := by
    intro v hv
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hv
    apply (mem_smul_iff_gauge_le hconv hclosed hK₀ hbdd
      (Nat.cast_nonneg _) _).mpr
    rw [intVectorToReal_stepsHom]
    change gauge K (∑ i, (c i : ℝ) • intVectorToReal (stepZ i)) ≤ _
    simp_rw [hstepReal]
    convert B.gauge_sum_le hconv hK₀ (fun x hx ↦ (hsymm x).mp hx) hc using 1
    norm_num
  refine ⟨C, hTcard ▸ ?_⟩
  exact card_le_pow_mul_card_of_mem_convex_dilate D T hconv
    (mem_of_mem_nhds hK₀) hsymm hDK hTmem

end

end ChangFreimanRuzsa
