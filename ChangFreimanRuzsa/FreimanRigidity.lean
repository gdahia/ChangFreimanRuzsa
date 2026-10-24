/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GapToolkit
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Tactic.Abel

/-!
# Transport of a progression across a Freiman isomorphism

In the proof of Chang's theorem for `X : Finset (ZMod q)`, `ChangFreimanRuzsa.RuzsaModel` gives a
Freiman `8`-isomorphism from a subset `X₁ ⊆ X` onto a set `Y : Finset (ZMod m)`, and
`ChangFreimanRuzsa.Fourier` and `ChangFreimanRuzsa.BohrProgression` give a proper progression
inside `Y + Y - (Y + Y)`. This file transports that progression back to `X₁ + X₁ - (X₁ + X₁)`.
The statements hold in arbitrary abelian groups.

## Main statements

* `GAP.apply_origin_add_linearCombination`: on the carrier of a GAP `Q`, a Freiman
  `2`-homomorphism `f` is affine. It sends `Q.origin + ∑ i, w i • Q.step i` to
  `f Q.origin + ∑ i, w i • (f (Q.origin + Q.step i) - f Q.origin)`.
* `GAP.exists_proper_carrier_eq_image_of_isAddFreimanIso`: a Freiman `2`-isomorphism defined on
  the carrier of a proper GAP maps it onto a proper GAP of at most the same dimension.
* `card_add_le_of_isAddFreimanIso`: a Freiman `2`-isomorphism from `B` onto `A` satisfies
  `#(B + B) ≤ #(A + A)`.
* `exists_proper_gap_subset_add_sub_add_of_isAddFreimanIso`: a Freiman `8`-isomorphism from `A`
  onto `B` transports a proper GAP contained in `B + B - (B + B)` to a proper GAP of at most the
  same dimension and of the same cardinality contained in `A + A - (A + A)`.

The order `8` is needed because a relation `z₁ + z₂ = z₃ + z₄` between elements of
`B + B - (B + B)` unfolds into a relation between eight elements of `B` on each side.
-/

public section

namespace ChangFreimanRuzsa

open Finset Function
open scoped Pointwise

noncomputable section

/-- A function `w` with `w i ≠ 0` is the sum of a function and the indicator of `i`. -/
private lemma exists_eq_add_single {ι : Type*} [DecidableEq ι] {w : ι → ℕ} {i : ι}
    (hi : w i ≠ 0) : ∃ u, w = u + Pi.single (M := fun _ ↦ ℕ) i 1 := by
  refine ⟨update w i (w i - 1), ?_⟩
  ext j
  rcases eq_or_ne j i with rfl | hj <;> simp [*]
  grind

namespace GAP

variable {G H : Type*} [DecidableEq G] [AddCommGroup G] [DecidableEq H] [AddCommGroup H]

/-! ### Rigidity of a progression under a Freiman 2-homomorphism -/

lemma origin_add_linearCombination_mem (Q : GAP H) {w : Fin Q.dim → ℕ}
    (hw : ∀ i, w i < Q.length i) : Q.origin + Fintype.linearCombination ℕ Q.step w ∈ Q.carrier := by
  rw [Q.carrier_eq, mem_image]
  exact ⟨fun i ↦ ⟨w i, hw i⟩, mem_univ _, rfl⟩

omit [DecidableEq G] in
/-- Adding the `i`-th step inside the carrier of a GAP `Q` changes the image under a Freiman
`2`-homomorphism `f` by `f (Q.origin + Q.step i) - f Q.origin`. -/
lemma apply_add_step (Q : GAP H) {B : Set G} {f : H → G}
    (hf : IsAddFreimanHom 2 (Q.carrier : Set H) B f) {i : Fin Q.dim} {x : H}
    (hx : x ∈ Q.carrier) (hxi : x + Q.step i ∈ Q.carrier) (hi : Q.origin + Q.step i ∈ Q.carrier) :
    f (x + Q.step i) = f x + (f (Q.origin + Q.step i) - f Q.origin) := by
  rw [← add_sub_assoc, eq_sub_iff_add_eq]
  exact hf.add_eq_add hxi Q.origin_mem hx hi (by abel)

omit [DecidableEq G] in
/-- On the carrier of a GAP `Q`, a Freiman `2`-homomorphism `f` is affine: it sends
`Q.origin + ∑ i, w i • Q.step i` to
`f Q.origin + ∑ i, w i • (f (Q.origin + Q.step i) - f Q.origin)`. -/
lemma apply_origin_add_linearCombination (Q : GAP H) {B : Set G} {f : H → G}
    (hf : IsAddFreimanHom 2 (Q.carrier : Set H) B f) {w : Fin Q.dim → ℕ}
    (hw : ∀ i, w i < Q.length i) :
    f (Q.origin + Fintype.linearCombination ℕ Q.step w) =
      f Q.origin +
        Fintype.linearCombination ℕ (fun i ↦ f (Q.origin + Q.step i) - f Q.origin) w := by
  induction w using WellFoundedLT.induction with
  | _ w ih =>
  obtain rfl | ⟨i, hi : w i ≠ 0⟩ := (eq_or_ne w 0).imp_right Function.ne_iff.1
  · simp
  obtain ⟨u, rfl⟩ := exists_eq_add_single hi
  have hu : ∀ j, u j < Q.length j := fun j ↦ (Nat.le_add_right _ _).trans_lt (hw j)
  have hw' := Q.origin_add_linearCombination_mem hw
  simp only [map_add, Fintype.linearCombination_apply_single, one_smul, ← add_assoc] at hw' ⊢
  rw [Q.apply_add_step hf (Q.origin_add_linearCombination_mem hu) hw' (by
    simpa using Q.origin_add_linearCombination_mem fun j ↦ (Nat.le_add_left _ _).trans_lt (hw j)),
    ih u (Pi.lt_def.2 ⟨fun j ↦ Nat.le_add_right _ _, i, by simp⟩) hu]

/-- The image of a GAP `Q` under a Freiman `2`-homomorphism `f` is the progression with origin
`f Q.origin`, steps `f (Q.origin + Q.step i) - f Q.origin` and the same lengths. -/
lemma image_gapMap_eq_image (Q : GAP H) {B : Set G} {f : H → G}
    (hf : IsAddFreimanHom 2 (Q.carrier : Set H) B f) :
    univ.image (gapMap (f Q.origin) (fun i ↦ f (Q.origin + Q.step i) - f Q.origin) Q.length) =
      Q.carrier.image f := by
  rw [Q.carrier_eq, image_image]
  congr with w
  exact (Q.apply_origin_add_linearCombination hf fun i ↦ (w i).isLt).symm

/-- A Freiman `2`-isomorphism defined on the carrier of a proper GAP maps it onto a proper GAP of
at most the same dimension, with the same lengths.

The image is proper because it has `∏ i, Q.length i` elements, so its coefficient map is
injective. -/
lemma exists_proper_carrier_eq_image_of_isAddFreimanIso {Q : GAP H} (hQ : Q.Proper) {B : Set G}
    {f : H → G} (hf : IsAddFreimanIso 2 (Q.carrier : Set H) B f) :
    ∃ R : GAP G, R.Proper ∧ R.dim ≤ Q.dim ∧ R.carrier = Q.carrier.image f := by
  have himage := Q.image_gapMap_eq_image hf.isAddFreimanHom
  refine ⟨ofSteps (f Q.origin) (fun i ↦ f (Q.origin + Q.step i) - f Q.origin) Q.length,
    proper_ofSteps Q.length_pos ?_, dim_ofSteps_le, (carrier_ofSteps Q.length_pos).trans himage⟩
  rw [← Set.injOn_univ, ← coe_univ]
  apply injOn_of_card_image_eq
  rw [himage, card_image_of_injOn hf.bijOn.injOn, Q.card_eq_prod_length hQ, card_univ,
    Fintype.card_pi]
  simp

end GAP

/-! ### Transport along a Freiman 8-isomorphism -/

variable {G H : Type*} [DecidableEq G] [AddCommGroup G] [DecidableEq H] [AddCommGroup H]

/-- A Freiman `2`-isomorphism `ψ` from `B` onto `A` satisfies `#(B + B) ≤ #(A + A)`: the map
`a + b ↦ ψ a + ψ b` is well defined and injective on `B + B`. -/
lemma card_add_le_of_isAddFreimanIso {A : Finset G} {B : Finset H} {ψ : H → G}
    (hψ : IsAddFreimanIso 2 (B : Set H) (A : Set G) ψ) : #(B + B) ≤ #(A + A) := by
  have hB {z : H} (hz : z ∈ B + B) :
      z ∈ (fun (a, b) ↦ a + b) '' ((B : Set H) ×ˢ (B : Set H)) := by
    rw [Set.add_image_prod]
    exact_mod_cast hz
  apply card_le_card_of_injOn
    ((fun (a, b) ↦ ψ a + ψ b) ∘ invFunOn (fun (a, b) ↦ a + b) ((B : Set H) ×ˢ (B : Set H)))
  · intro z hz
    obtain ⟨ha, hb⟩ := invFunOn_mem (hB hz)
    exact add_mem_add (hψ.bijOn.mapsTo ha) (hψ.bijOn.mapsTo hb)
  · intro z hz z' hz' hzz
    obtain ⟨ha, hb⟩ := invFunOn_mem (hB hz)
    obtain ⟨ha', hb'⟩ := invFunOn_mem (hB hz')
    rw [← invFunOn_eq (hB hz), ← invFunOn_eq (hB hz')]
    exact (hψ.add_eq_add ha hb ha' hb').1 hzz

/-- The map induced on `B + B - (B + B)` by a map `ψ` defined on `B`. It sends `a + b - c - d` to
`ψ a + ψ b - ψ c - ψ d` for a chosen representation. -/
private def signedTransport (B : Finset H) (ψ : H → G) : H → G :=
  (fun (a, b, c, d) ↦ ψ a + ψ b - ψ c - ψ d) ∘
    invFunOn (fun (a, b, c, d) ↦ a + b - c - d)
      ((B : Set H) ×ˢ (B : Set H) ×ˢ (B : Set H) ×ˢ (B : Set H))

omit [DecidableEq G] in
private lemma signedTransport_spec {B : Finset H} (ψ : H → G) {z : H}
    (hz : z ∈ (B + B) - (B + B)) :
    ∃ a ∈ B, ∃ b ∈ B, ∃ c ∈ B, ∃ d ∈ B,
      z = a + b - c - d ∧ signedTransport B ψ z = ψ a + ψ b - ψ c - ψ d := by
  have hB : z ∈ (fun (a, b, c, d) ↦ a + b - c - d) ''
      ((B : Set H) ×ˢ (B : Set H) ×ˢ (B : Set H) ×ˢ (B : Set H)) := by
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_sub.1 hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.1 hu
    obtain ⟨c, hc, d, hd, rfl⟩ := mem_add.1 hv
    exact ⟨(a, b, c, d), ⟨ha, hb, hc, hd⟩, sub_sub _ _ _⟩
  obtain ⟨ha, hb, hc, hd⟩ := invFunOn_mem hB
  exact ⟨_, ha, _, hb, _, hc, _, hd, (invFunOn_eq hB).symm, rfl⟩

private lemma signedTransport_mem {A : Finset G} {B : Finset H} {ψ : H → G}
    (hψ : Set.MapsTo ψ B A) {z : H} (hz : z ∈ (B + B) - (B + B)) :
    signedTransport B ψ z ∈ (A + A) - (A + A) := by
  obtain ⟨a, ha, b, hb, c, hc, d, hd, -, hz⟩ := signedTransport_spec ψ hz
  rw [hz, sub_sub]
  exact sub_mem_sub (add_mem_add (hψ ha) (hψ hb)) (add_mem_add (hψ hc) (hψ hd))

omit [DecidableEq G] in
/-- If `ψ` is a Freiman `8`-isomorphism on `B`, then the induced map on a subset `S` of
`B + B - (B + B)` is a Freiman `2`-isomorphism: a relation `z₁ + z₂ = z₃ + z₄` has eight terms of
`B` on each side. -/
private lemma isAddFreimanIso_signedTransport {A : Finset G} {B : Finset H} {ψ : H → G}
    (hψ : IsAddFreimanIso 8 (B : Set H) (A : Set G) ψ) {S : Set H}
    (hS : S ⊆ (((B + B) - (B + B) : Finset H) : Set H)) :
    IsAddFreimanIso 2 S (signedTransport B ψ '' S) (signedTransport B ψ) := by
  have h : ∀ z₁ ∈ S, ∀ z₂ ∈ S, ∀ z₃ ∈ S, ∀ z₄ ∈ S,
      signedTransport B ψ z₁ + signedTransport B ψ z₂ =
        signedTransport B ψ z₃ + signedTransport B ψ z₄ ↔ z₁ + z₂ = z₃ + z₄ := by
    intro z₁ h₁ z₂ h₂ z₃ h₃ z₄ h₄
    obtain ⟨a₁, ha₁, b₁, hb₁, c₁, hc₁, d₁, hd₁, rfl, hg₁⟩ := signedTransport_spec ψ (hS h₁)
    obtain ⟨a₂, ha₂, b₂, hb₂, c₂, hc₂, d₂, hd₂, rfl, hg₂⟩ := signedTransport_spec ψ (hS h₂)
    obtain ⟨a₃, ha₃, b₃, hb₃, c₃, hc₃, d₃, hd₃, rfl, hg₃⟩ := signedTransport_spec ψ (hS h₃)
    obtain ⟨a₄, ha₄, b₄, hb₄, c₄, hc₄, d₄, hd₄, rfl, hg₄⟩ := signedTransport_spec ψ (hS h₄)
    have h := hψ.map_sum_eq_map_sum
      (s := a₁ ::ₘ b₁ ::ₘ a₂ ::ₘ b₂ ::ₘ c₃ ::ₘ d₃ ::ₘ c₄ ::ₘ {d₄})
      (t := a₃ ::ₘ b₃ ::ₘ a₄ ::ₘ b₄ ::ₘ c₁ ::ₘ d₁ ::ₘ c₂ ::ₘ {d₂})
      (by simp [*]) (by simp [*]) (by simp) (by simp)
    simp only [Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons,
      Multiset.sum_singleton, ← sub_eq_zero (b := _ + _)] at h
    rw [hg₁, hg₂, hg₃, hg₄, ← sub_eq_zero, ← sub_eq_zero (a := _ + _)]
    convert h using 2 <;> abel
  refine isAddFreimanIso_two.2 ⟨Set.InjOn.bijOn_image ?_, h⟩
  intro x hx y hy hxy
  exact add_right_cancel ((h x hx y hy y hy y hy).1 (by rw [hxy]))

/-- A Freiman `8`-isomorphism from `A` onto `B` transports a proper progression contained in
`B + B - (B + B)` to a proper progression of at most the same dimension and of the same
cardinality contained in `A + A - (A + A)`. -/
lemma exists_proper_gap_subset_add_sub_add_of_isAddFreimanIso {A : Finset G} {B : Finset H}
    {φ : G → H} (hφ : IsAddFreimanIso 8 (A : Set G) (B : Set H) φ) {Q : GAP H} (hQ : Q.Proper)
    (hQB : Q.carrier ⊆ (B + B) - (B + B)) :
    ∃ R : GAP G, R.Proper ∧ R.dim ≤ Q.dim ∧ R.carrier.card = Q.carrier.card ∧
      R.carrier ⊆ (A + A) - (A + A) := by
  have hf := isAddFreimanIso_signedTransport hφ.invFunOn (coe_subset.2 hQB)
  obtain ⟨R, hR, hRdim, hRQ⟩ := GAP.exists_proper_carrier_eq_image_of_isAddFreimanIso hQ hf
  refine ⟨R, hR, hRdim, ?_, ?_⟩ <;> rw [hRQ]
  · exact card_image_of_injOn hf.bijOn.injOn
  · rw [image_subset_iff]
    intro z hz
    exact signedTransport_mem hφ.invFunOn.bijOn.mapsTo (hQB hz)

end

end ChangFreimanRuzsa
