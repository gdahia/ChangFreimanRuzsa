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

Let $L$ be a subgroup of a real normed space $E$ and let $K \subseteq E$. A
`GaugeControlledLatticeBox L K s A` consists of linearly independent vectors
$b_1, \dots, b_s \in L$ and half-widths $m_1, \dots, m_s \in \mathbb{N}$ such that every point of
$K \cap L$ is $\sum_i c_i b_i$ with $c_i \in \mathbb{Z}$ and $|c_i| \le m_i$, and
$m_i \, g_K(b_i) \le A$ for every $i$, where $g_K$ is the gauge of $K$.

If $K$ is a symmetric convex neighbourhood of $0$, then every combination $\sum_i c_i b_i$ with
$|c_i| \le m_i$ has gauge at most $s A$. For the lattice $\mathbb{Z}^s \subseteq \mathbb{R}^s$ and
$A = a \in \mathbb{N}$, the coefficient box therefore maps into $s a K$, and the residue estimate
`card_le_pow_mul_card_of_mem_convex_dilate` turns the box into an `AdaptedLatticeBox` for
$D = K \cap \mathbb{Z}^s$ with $\prod_i (2 m_i + 1) \le (2 s a + 1)^s |D|$.

The file also defines the dilations $A_0 = 0$, $A_{s+1} = 1 + 4 s A_s$ of the shortest-vector
induction and proves the elementary facts that the induction uses.
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

/-- The gauge bounds $A_0 = 0$ and $A_{s+1} = 1 + 4 s A_s$ of the shortest-vector induction. -/
def gaugeReboxingDilation : ℕ → ℕ
  | 0 => 0
  | s + 1 => 1 + 4 * s * gaugeReboxingDilation s

/-- The factor $(2 s A_s + 1)^s$, where $A_s$ is `gaugeReboxingDilation s`. -/
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
      rw [gaugeReboxingDilation, pow_succ]
      have hpow := Nat.pow_le_pow_left (by grind : 4 * s + 1 ≤ 4 * (s + 1) + 1) s
      have hone : 1 ≤ (4 * (s + 1) + 1) ^ s := one_le_pow₀ (by grind)
      nlinarith [Nat.mul_le_mul_left (4 * s) (ih.trans hpow)]

lemma boxReboxingFactor_le_pow (s : ℕ) :
    boxReboxingFactor s ≤ (4 * s + 1) ^ ((s + 2) * s) := by
  have hone : 1 ≤ (4 * s + 1) ^ s := one_le_pow₀ (by grind)
  rw [boxReboxingFactor, pow_mul]
  apply Nat.pow_le_pow_left
  rw [pow_add]
  nlinarith [Nat.mul_le_mul_left (2 * s) (gaugeReboxingDilation_le_pow s),
    Nat.mul_le_mul_left ((4 * s + 1) ^ s) (by nlinarith : 2 * s + 1 ≤ (4 * s + 1) ^ 2)]

/-- In a space of dimension $0$, the empty family is a gauge-controlled lattice box with
$A = 0$. -/
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

/-- If $K \cap L$ spans $E$ and $\pi : E \to F$ is a surjective linear map, then
$\pi(K) \cap \pi(L)$ spans $F$. -/
lemma span_inter_image_map_eq_top
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : AddSubgroup E) (K : Set E) (π : E →ₗ[ℝ] F)
    (hπ : Function.Surjective π)
    (hspan : Submodule.span ℝ (K ∩ (L : Set E)) = ⊤) :
    Submodule.span ℝ
      ((π '' K) ∩ ((L.map (π : E →+ F)) : Set F)) = ⊤ := by
  rw [eq_top_iff, ← LinearMap.range_eq_top.mpr hπ, LinearMap.range_eq_map, ← hspan,
    Submodule.map_span]
  apply Submodule.span_mono
  rintro _ ⟨x, ⟨hxK, hxL⟩, rfl⟩
  exact ⟨⟨x, hxK, rfl⟩, AddSubgroup.mem_map_of_mem _ hxL⟩

/-- If $K$ is a closed bounded convex neighbourhood of $0$ and $K \cap L$ contains a nonzero
point, then $L$ has a nonzero point $v$ of positive minimal gauge among the nonzero points
of $L$. -/
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
  obtain ⟨hvL, hvK⟩ := hw 0
  have hgaugele : gauge K (w 0) ≤ successiveMinimum L K 1 :=
    (mem_smul_iff_gauge_le hconv hclosed hK₀ hvonN (successiveMinimum_nonneg L K 1) _).mp hvK
  have hfirst : ∀ y ∈ L, y ≠ 0 → successiveMinimum L K 1 ≤ gauge K y := by
    intro y hy hyne
    exact successiveMinimum_le (gauge_nonneg y) ⟨fun _ ↦ y, linearIndependent_unique_iff.mpr hyne,
      fun _ ↦ ⟨hy, (mem_smul_iff_gauge_le hconv hclosed hK₀ hvonN (gauge_nonneg y) y).mpr le_rfl⟩⟩
  have hlampos : 0 < successiveMinimum L K 1 := by
    obtain ⟨R, hR⟩ := hbdd.subset_closedBall (0 : E)
    obtain ⟨r, hrpos, hr⟩ := exists_pos_forall_norm_lt L
    have hxpos : 0 < r / (2 * max R 1) := div_pos hrpos (by positivity)
    refine hxpos.trans_le (le_successiveMinimum_one
      (hR.trans (closedBall_subset_closedBall (le_max_left R 1))) hr hxpos.le ?_ hne1)
    nlinarith [div_mul_cancel₀ r (by positivity : (2 * max R 1 : ℝ) ≠ 0),
      mul_pos hxpos (lt_max_of_lt_right zero_lt_one : (0 : ℝ) < max R 1)]
  refine ⟨w 0, hvL, hwindep.ne_zero 0, hlampos.trans_le (hfirst _ hvL (hwindep.ne_zero 0)), ?_⟩
  intro y hy hyne
  exact hgaugele.trans (hfirst y hy hyne)

/-- Endpoint gauge bounds control every linear combination in the centered integer box. -/
lemma gauge_sum_zsmul_le_card_mul
    (hconv : Convex ℝ K) (hK₀ : K ∈ 𝓝 0) (hsymm : ∀ x ∈ K, -x ∈ K)
    (step : Fin s → E) (m : Fin s → ℕ) {A : ℝ}
    (hend : ∀ i, (m i : ℝ) * gauge K (step i) ≤ A)
    {c : Fin s → ℤ} (hc : c ∈ intBox m) :
    gauge K (∑ i, (c i : ℝ) • step i) ≤ s * A := by
  refine (gauge_sum_le hconv (absorbent_nhds_zero hK₀) Finset.univ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ A ?_).trans_eq (by simp)
  intro i _
  rw [gauge_smul_abs hsymm]
  refine (mul_le_mul_of_nonneg_right ?_ (gauge_nonneg (step i))).trans (hend i)
  exact_mod_cast mem_intBox.mp hc i

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
  have hi := Fintype.linearIndependent_iff.mp B.step_independent
    (fun j ↦ ((c j - c' j : ℤ) : ℝ)) (by simpa [sub_smul, sub_eq_zero] using h) i
  simpa [sub_eq_zero] using hi

/-- If $\nu \le \mu + \lambda / 2$, $\lambda \le 2 \mu$ and $m \mu \le A$, then
$m \nu \le 2 A$. This bounds the endpoint of a lifted step. -/
lemma endpoint_gauge_lift_le_two_mul {m : ℕ} {A lam μ ν : ℝ}
    (hν : ν ≤ μ + lam / 2) (hlam : lam ≤ 2 * μ)
    (hend : (m : ℝ) * μ ≤ A) :
    (m : ℝ) * ν ≤ 2 * A := by
  nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

lemma intVectorToReal_stepsHom (step : Fin s → (Fin s → ℤ)) (c : Fin s → ℤ) :
    intVectorToReal (stepsHom step c) =
      ∑ i, (c i : ℝ) • intVectorToReal (step i) := by
  change intVectorToReal (∑ i, c i • step i) = _
  rw [intVectorToReal_sum]
  congr with i : 1
  rw [intVectorToReal_zsmul, Int.cast_smul_eq_zsmul]

/-- Let $K \subseteq \mathbb{R}^s$ be a closed bounded symmetric convex neighbourhood of $0$ and
let $D = K \cap \mathbb{Z}^s$. A gauge-controlled box for $\mathbb{Z}^s$ and $K$ with gauge bound
$a$ gives an adapted lattice box for $D$ with $\prod_i (2 m_i + 1) \le (2 s a + 1)^s |D|$. -/
lemma GaugeControlledLatticeBox.exists_adaptedLatticeBox
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
  have hstepReal : ∀ i, intVectorToReal (stepZ i) = B.step i := hstep
  let C : AdaptedLatticeBox D := {
    step := stepZ
    halfWidth := B.halfWidth
    stepHom_injective := by
      intro c c' hcc'
      apply B.sum_injective
      have hreal := congr_arg intVectorToReal hcc'
      simp_rw [intVectorToReal_stepsHom, hstepReal] at hreal
      exact hreal
    mem_stepBox := by
      intro x hx
      obtain ⟨c, hc, hcx⟩ := B.cover (intVectorToReal x) ((hDK x).mp hx)
        (AddSubgroup.mem_map_of_mem _ (AddSubgroup.mem_top x))
      refine ⟨c, hc, intVectorToReal_injective ?_⟩
      simp_rw [intVectorToReal_stepsHom, hstepReal]
      exact hcx
  }
  refine ⟨C, ?_⟩
  rw [← card_intBox, ← Finset.card_image_of_injective _ C.stepHom_injective]
  apply card_le_pow_mul_card_of_mem_convex_dilate D _ hconv (mem_of_mem_nhds hK₀) hsymm hDK
  intro v hv
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hv
  apply (mem_smul_iff_gauge_le hconv hclosed hK₀ hbdd (Nat.cast_nonneg _) _).mpr
  rw [intVectorToReal_stepsHom]
  change gauge K (∑ i, (c i : ℝ) • intVectorToReal (stepZ i)) ≤ _
  simp_rw [hstepReal]
  convert B.gauge_sum_le hconv hK₀ (fun x hx ↦ (hsymm x).mp hx) hc using 1
  norm_num

end

end ChangFreimanRuzsa
