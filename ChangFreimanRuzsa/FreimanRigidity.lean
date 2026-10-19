/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import ChangFreimanRuzsa.GapToolkit
import Mathlib.Data.Rat.Floor

/-! # Transport of a progression across a Freiman isomorphism

In the proof of Chang's theorem for $X \subseteq \mathbb{Z}/q\mathbb{Z}$,
`ChangFreimanRuzsa.RuzsaModel` gives a Freiman $8$-isomorphism from a subset $X_1 \subseteq X$
onto a set $Y \subseteq \mathbb{Z}/m\mathbb{Z}$, and `ChangFreimanRuzsa.Fourier` and
`ChangFreimanRuzsa.BohrProgression` give a proper progression inside $2Y - 2Y$. This file
transports that progression back to $2X_1 - 2X_1$. The statements hold in arbitrary abelian
groups.

## Main results

* `GAP.exists_map_of_isAddFreimanIso`: a Freiman $2$-isomorphism defined on the carrier of a proper
  GAP maps it onto a proper GAP of the same dimension and the same lengths. The steps of the image
  are the images of the one-step displacements, and the image is proper because it has as many
  elements as the original progression.
* `exists_transported_gap`: a Freiman $8$-isomorphism $\varphi$ from $A$ onto $B$ transports a
  proper GAP contained in $(B + B) - (B + B)$ to a proper GAP of the same dimension and cardinality
  contained in $(A + A) - (A + A)$.

The order $8$ is needed because a relation $z_1 + z_2 = z_3 + z_4$ between elements of
$(B + B) - (B + B)$ unfolds into a relation between eight elements of $B$ on each side.
-/

@[expose] public section

namespace ChangFreimanRuzsa

open scoped Pointwise

noncomputable section

/-- Two equations with the same difference are equivalent. -/
private lemma eq_iff_eq_of_sub_eq_sub {M : Type*} [AddCommGroup M] {u v u' v' : M}
    (h : u - v = u' - v') : u = v ↔ u' = v' := by
  rw [← sub_eq_zero, ← sub_eq_zero (a := u'), h]

/-- Splitting off one unit of the `i`-th coefficient from an `ℕ`-linear combination. -/
private lemma sum_nsmul_eq_update_add_single {d : ℕ} {M : Type*} [AddCommMonoid M]
    (w : Fin d → ℕ) (σ : Fin d → M) {i : Fin d} (hi : w i ≠ 0) :
    ∑ j, w j • σ j =
      (∑ j, Function.update w i (w i - 1) j • σ j) +
        ∑ j, (Pi.single i 1 : Fin d → ℕ) j • σ j := by
  rw [← Finset.sum_add_distrib]
  congr with j
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self, Pi.single_eq_same, ← add_nsmul]
    congr 1
    grind
  · rw [Function.update_of_ne hj, Pi.single_eq_of_ne hj, zero_smul, add_zero]

private lemma sum_single_nsmul {d : ℕ} {M : Type*} [AddCommMonoid M] (σ : Fin d → M) (i : Fin d) :
    ∑ j, (Pi.single i 1 : Fin d → ℕ) j • σ j = σ i := by
  simp [Pi.single_apply, one_nsmul]

namespace GAP

variable {G H : Type*} [DecidableEq G] [AddCommGroup G] [DecidableEq H] [AddCommGroup H]

/-! ### Rigidity of a progression under a Freiman 2-isomorphism -/

/-- A point of the coefficient box of a GAP, written with `ℕ`-valued coefficients. Unlike
`gapMap`, the coefficients are unconstrained, which is what makes induction on their sum
available. -/
def natPoint (Q : GAP H) (w : Fin Q.dim → ℕ) : H := Q.origin + ∑ i, w i • Q.step i

lemma natPoint_gapMap (Q : GAP H) (w : (i : Fin Q.dim) → Fin (Q.length i)) :
    Q.natPoint (fun i ↦ (w i : ℕ)) = gapMap Q.origin Q.step Q.length w := rfl

lemma natPoint_zero (Q : GAP H) : Q.natPoint 0 = Q.origin := by
  simp [natPoint]

lemma natPoint_mem (Q : GAP H) {w : Fin Q.dim → ℕ} (hw : ∀ i, w i < Q.length i) :
    Q.natPoint w ∈ Q.carrier := by
  rw [Q.carrier_eq, Finset.mem_image]
  exact ⟨fun i ↦ ⟨w i, hw i⟩, Finset.mem_univ _, rfl⟩

lemma origin_mem (Q : GAP H) : Q.origin ∈ Q.carrier := by
  simpa [Q.natPoint_zero] using Q.natPoint_mem (w := 0) fun j ↦ Q.length_pos j

lemma single_lt_length (Q : GAP H) (i : Fin Q.dim) {k : ℕ} (hk : k < Q.length i) (j : Fin Q.dim) :
    (Pi.single i k : Fin Q.dim → ℕ) j < Q.length j := by
  rw [Pi.single_apply]
  by_cases hj : j = i
  · subst hj
    simpa using hk
  · simpa [hj] using Q.length_pos j

/-- The step of the transported progression in direction `i`: the displacement of the image of the
origin under one unit of the `i`-th coefficient. The truncation `min 1 (length i - 1)` keeps the
coefficient inside the box; in the degenerate case `length i = 1` the coefficient is always `0`, so
the value of the step is irrelevant. -/
def transportStep (Q : GAP H) (f : H → G) (i : Fin Q.dim) : G :=
  f (Q.natPoint (Pi.single i (min 1 (Q.length i - 1)))) - f Q.origin

omit [DecidableEq G] in
lemma transportStep_of_one_lt (Q : GAP H) (f : H → G) {i : Fin Q.dim} (hi : 1 < Q.length i) :
    Q.transportStep f i = f (Q.natPoint (Pi.single i 1)) - f Q.origin := by
  rw [transportStep, min_eq_left (by grind)]

/-- One unit of the `i`-th coefficient is an additive quadruple inside the coefficient box. -/
lemma natPoint_add_origin (Q : GAP H) (w : Fin Q.dim → ℕ) {i : Fin Q.dim} (hi : w i ≠ 0) :
    Q.natPoint w + Q.origin =
      Q.natPoint (Function.update w i (w i - 1)) + Q.natPoint (Pi.single i 1) := by
  rw [natPoint, natPoint, natPoint, sum_nsmul_eq_update_add_single w Q.step hi]
  abel

/-- **Rigidity.** On the carrier of a proper GAP, a Freiman `2`-isomorphism is affine: the image of
a box point is the image of the origin displaced by the same coefficients along the transported
steps. -/
lemma apply_natPoint (Q : GAP H) {f : H → G}
    (hf : IsAddFreimanIso 2 (Q.carrier : Set H) ((Q.carrier.image f : Finset G) : Set G) f)
    {w : Fin Q.dim → ℕ} (hw : ∀ i, w i < Q.length i) :
    f (Q.natPoint w) = f Q.origin + ∑ i, w i • Q.transportStep f i := by
  induction hn : ∑ i, w i generalizing w with
  | zero =>
    obtain rfl : w = 0 := funext fun i ↦ Finset.sum_eq_zero_iff.1 hn i (Finset.mem_univ i)
    simp [Q.natPoint_zero]
  | succ n ih =>
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra! hcon
      simp [hcon] at hn
    have hilen : 1 < Q.length i := by grind [hw i]
    have hupdlt : ∀ j, Function.update w i (w i - 1) j < Q.length j := by
      intro j
      rw [Function.update_apply]
      grind [hw j]
    have hβ : f (Q.natPoint w) - f (Q.natPoint (Function.update w i (w i - 1))) =
        Q.transportStep f i := by
      rw [Q.transportStep_of_one_lt f hilen, sub_eq_sub_iff_add_eq_add]
      exact ((hf.add_eq_add (Q.natPoint_mem hw) Q.origin_mem (Q.natPoint_mem hupdlt)
        (Q.natPoint_mem (Q.single_lt_length i hilen))).2 (Q.natPoint_add_origin w hi)).trans
        (add_comm _ _)
    rw [sub_eq_iff_eq_add] at hβ
    rw [hβ, ih hupdlt, sum_nsmul_eq_update_add_single w (Q.transportStep f) hi, sum_single_nsmul]
    · abel
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) w] at hn
    rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
    grind

/-- **Rigidity of a GAP under a Freiman 2-isomorphism.** A Freiman $2$-isomorphism defined on the
carrier of a proper GAP sends it to a proper GAP of the same dimension and the same lengths.

The image is proper because it has $\prod_i \ell_i$ elements, so its coefficient map is
injective. -/
lemma exists_map_of_isAddFreimanIso (Q : GAP H) (hQ : Q.Proper) {f : H → G}
    (hf : IsAddFreimanIso 2 (Q.carrier : Set H) ((Q.carrier.image f : Finset G) : Set G) f) :
    ∃ R : GAP G, R.Proper ∧ R.dim = Q.dim ∧ R.carrier = Q.carrier.image f := by
  have himage : Finset.univ.image (gapMap (f Q.origin) (Q.transportStep f) Q.length) =
      Q.carrier.image f := by
    ext y
    simp only [Finset.mem_image, Q.carrier_eq]
    constructor
    · rintro ⟨w, -, rfl⟩
      refine ⟨gapMap Q.origin Q.step Q.length w, ⟨w, Finset.mem_univ _, rfl⟩, ?_⟩
      rw [← Q.natPoint_gapMap w, Q.apply_natPoint hf fun i ↦ (w i).2]
      rfl
    · rintro ⟨x, ⟨w, -, rfl⟩, rfl⟩
      refine ⟨w, Finset.mem_univ _, ?_⟩
      rw [← Q.natPoint_gapMap w, Q.apply_natPoint hf fun i ↦ (w i).2]
      rfl
  refine ⟨⟨Q.dim, Q.carrier.image f, f Q.origin, Q.transportStep f, Q.length, Q.length_pos,
    himage.symm⟩, ?_, rfl, rfl⟩
  change Function.Injective (gapMap (f Q.origin) (Q.transportStep f) Q.length)
  rw [← Set.injOn_univ, ← Finset.coe_univ]
  apply Finset.injOn_of_card_image_eq
  rw [himage, Finset.card_image_of_injOn hf.bijOn.injOn, Q.card_eq_prod_length hQ,
    Finset.card_univ, Fintype.card_pi]
  simp

end GAP

/-! ### Signed-sum extension of a Freiman 8-isomorphism -/

variable {G H : Type*} [DecidableEq G] [AddCommGroup G] [DecidableEq H] [AddCommGroup H]

open scoped Classical in
/-- A quadruple $(a, b, c, d)$ of elements of $B$ with $z = a + b - c - d$, when one exists. -/
private def signedRep (B : Finset H) (z : H) : H × H × H × H :=
  if h : ∃ p : H × H × H × H, (p.1 ∈ B ∧ p.2.1 ∈ B ∧ p.2.2.1 ∈ B ∧ p.2.2.2 ∈ B) ∧
      z = p.1 + p.2.1 - p.2.2.1 - p.2.2.2 then h.choose else (z, z, z, z)

/-- The map induced on `(B + B) - (B + B)` by a map defined on `B`, along the chosen signed
representations. -/
private def signedTransport (B : Finset H) (ψ : H → G) (z : H) : G :=
  ψ (signedRep B z).1 + ψ (signedRep B z).2.1 - ψ (signedRep B z).2.2.1 -
    ψ (signedRep B z).2.2.2

omit [DecidableEq G] in
private lemma signedTransport_spec {B : Finset H} (ψ : H → G) {z : H}
    (hz : z ∈ (B + B) - (B + B)) :
    ∃ a ∈ B, ∃ b ∈ B, ∃ c ∈ B, ∃ d ∈ B,
      z = a + b - c - d ∧ signedTransport B ψ z = ψ a + ψ b - ψ c - ψ d := by
  have hex : ∃ p : H × H × H × H, (p.1 ∈ B ∧ p.2.1 ∈ B ∧ p.2.2.1 ∈ B ∧ p.2.2.2 ∈ B) ∧
      z = p.1 + p.2.1 - p.2.2.1 - p.2.2.2 := by
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.1 hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 hu
    obtain ⟨c, hc, d, hd, rfl⟩ := Finset.mem_add.1 hv
    exact ⟨(a, b, c, d), ⟨ha, hb, hc, hd⟩, by abel⟩
  rw [signedTransport, signedRep, dite_eq_left hex]
  obtain ⟨⟨ha, hb, hc, hd⟩, he⟩ := hex.choose_spec
  exact ⟨_, ha, _, hb, _, hc, _, hd, he, rfl⟩

open scoped Classical in
/-- A pair $(a, b)$ of elements of $B$ with $z = a + b$, when one exists. -/
private def pairRep (B : Finset H) (z : H) : H × H :=
  if h : ∃ p : H × H, (p.1 ∈ B ∧ p.2 ∈ B) ∧ z = p.1 + p.2 then h.choose else (z, z)

omit [DecidableEq G] in
private lemma pairRep_spec {B : Finset H} {z : H} (hz : z ∈ B + B) :
    ((pairRep B z).1 ∈ B ∧ (pairRep B z).2 ∈ B) ∧ z = (pairRep B z).1 + (pairRep B z).2 := by
  have hex : ∃ p : H × H, (p.1 ∈ B ∧ p.2 ∈ B) ∧ z = p.1 + p.2 := by
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 hz
    exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
  rw [pairRep, dite_eq_left hex]
  exact hex.choose_spec

/-- A Freiman `2`-isomorphism does not increase the size of the sumset: the induced map on sums of
two elements is injective, because a relation between two sums is reflected by the isomorphism. -/
lemma card_add_le_of_isAddFreimanIso {A : Finset G} {B : Finset H} {ψ : H → G}
    (hψ : IsAddFreimanIso 2 (B : Set H) (A : Set G) ψ) : (B + B).card ≤ (A + A).card := by
  apply Finset.card_le_card_of_injOn (fun z ↦ ψ (pairRep B z).1 + ψ (pairRep B z).2)
  · intro z hz
    obtain ⟨⟨h1, h2⟩, -⟩ := pairRep_spec (B := B) hz
    exact Finset.add_mem_add (hψ.bijOn.mapsTo h1) (hψ.bijOn.mapsTo h2)
  · intro z hz z' hz' hzz
    obtain ⟨⟨h1, h2⟩, he⟩ := pairRep_spec (B := B) hz
    obtain ⟨⟨h1', h2'⟩, he'⟩ := pairRep_spec (B := B) hz'
    rw [he, he']
    exact (hψ.add_eq_add h1 h2 h1' h2').1 hzz

/-- A Freiman $8$-isomorphism from $A$ onto $B$ transports a proper progression contained in
$(B + B) - (B + B)$ to a proper progression of the same dimension and cardinality contained in
$(A + A) - (A + A)$.

A relation $z_1 + z_2 = z_3 + z_4$ between signed sums of elements of $B$ has eight terms on each
side, so the $8$-isomorphism carries it to the corresponding relation in $A$. -/
lemma exists_transported_gap {A : Finset G} {B : Finset H} {φ : G → H}
    (hφ : IsAddFreimanIso 8 (A : Set G) (B : Set H) φ)
    (Q : GAP H) (hQ : Q.Proper) (hQsub : Q.carrier ⊆ (B + B) - (B + B)) :
    ∃ R : GAP G, R.Proper ∧ R.dim = Q.dim ∧ R.carrier.card = Q.carrier.card ∧
      R.carrier ⊆ (A + A) - (A + A) := by
  have hψ : IsAddFreimanIso 8 (B : Set H) (A : Set G) (Function.invFunOn φ (A : Set G)) :=
    hφ.invFunOn
  set ψ : H → G := Function.invFunOn φ (A : Set G) with hψdef
  set g : H → G := signedTransport B ψ with hgdef
  have hquad : ∀ z₁ ∈ (Q.carrier : Set H), ∀ z₂ ∈ (Q.carrier : Set H),
      ∀ z₃ ∈ (Q.carrier : Set H), ∀ z₄ ∈ (Q.carrier : Set H),
      (g z₁ + g z₂ = g z₃ + g z₄ ↔ z₁ + z₂ = z₃ + z₄) := by
    intro z₁ h₁ z₂ h₂ z₃ h₃ z₄ h₄
    obtain ⟨a₁, ha₁, b₁, hb₁, c₁, hc₁, d₁, hd₁, hz₁, hg₁⟩ :=
      signedTransport_spec ψ (hQsub (Finset.mem_coe.1 h₁))
    obtain ⟨a₂, ha₂, b₂, hb₂, c₂, hc₂, d₂, hd₂, hz₂, hg₂⟩ :=
      signedTransport_spec ψ (hQsub (Finset.mem_coe.1 h₂))
    obtain ⟨a₃, ha₃, b₃, hb₃, c₃, hc₃, d₃, hd₃, hz₃, hg₃⟩ :=
      signedTransport_spec ψ (hQsub (Finset.mem_coe.1 h₃))
    obtain ⟨a₄, ha₄, b₄, hb₄, c₄, hc₄, d₄, hd₄, hz₄, hg₄⟩ :=
      signedTransport_spec ψ (hQsub (Finset.mem_coe.1 h₄))
    have hiso := hψ.map_sum_eq_map_sum
      (s := a₁ ::ₘ b₁ ::ₘ a₂ ::ₘ b₂ ::ₘ c₃ ::ₘ d₃ ::ₘ c₄ ::ₘ {d₄})
      (t := a₃ ::ₘ b₃ ::ₘ a₄ ::ₘ b₄ ::ₘ c₁ ::ₘ d₁ ::ₘ c₂ ::ₘ {d₂})
      (by simp [*]) (by simp [*]) (by simp) (by simp)
    refine (eq_iff_eq_of_sub_eq_sub ?_).trans (hiso.trans (eq_iff_eq_of_sub_eq_sub ?_))
    · rw [hgdef, hg₁, hg₂, hg₃, hg₄]
      simp only [Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons,
        Multiset.sum_singleton]
      abel
    · rw [hz₁, hz₂, hz₃, hz₄]
      simp only [Multiset.sum_cons, Multiset.sum_singleton]
      abel
  have hinj : Set.InjOn g (Q.carrier : Set H) := by
    intro x hx y hy hxy
    refine add_right_cancel (b := y) ((hquad x hx y hy y hy y hy).1 ?_)
    rw [hxy]
  have hf : IsAddFreimanIso 2 (Q.carrier : Set H) ((Q.carrier.image g : Finset G) : Set G) g := by
    refine isAddFreimanIso_two.mpr ⟨?_, hquad⟩
    rw [Finset.coe_image]
    exact hinj.bijOn_image
  obtain ⟨R, hRproper, hRdim, hRcarrier⟩ := Q.exists_map_of_isAddFreimanIso hQ hf
  refine ⟨R, hRproper, hRdim, ?_, ?_⟩
  · rw [hRcarrier, Finset.card_image_of_injOn hinj]
  · rw [hRcarrier, Finset.image_subset_iff]
    intro z hz
    obtain ⟨a, ha, b, hb, c, hc, d, hd, -, hgz⟩ := signedTransport_spec ψ (hQsub hz)
    rw [hgdef, hgz, sub_sub]
    exact Finset.sub_mem_sub (Finset.add_mem_add (hψ.bijOn.mapsTo ha) (hψ.bijOn.mapsTo hb))
      (Finset.add_mem_add (hψ.bijOn.mapsTo hc) (hψ.bijOn.mapsTo hd))

end

end ChangFreimanRuzsa
