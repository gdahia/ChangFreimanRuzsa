/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.GAP.Basic
public import Mathlib.Combinatorics.Additive.FreimanHom
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Tactic.Abel

/-!
# Transport of a progression across a Freiman isomorphism

In the proof of Chang's theorem for `X : Finset (ZMod q)`,
`ChangFreimanRuzsa.BogolyubovRuzsa.RuzsaModel` gives a Freiman `8`-isomorphism from a subset
`X₁ ⊆ X` onto a set `Y : Finset (ZMod m)`, and `ChangFreimanRuzsa.BogolyubovRuzsa.Fourier` and
`ChangFreimanRuzsa.BogolyubovRuzsa.BohrSet` give a proper progression inside `Y + Y - (Y + Y)`. This
file transports that progression back to `X₁ + X₁ - (X₁ + X₁)`. The statements hold in arbitrary
abelian groups.

## Main definitions

* `GAP.freimanImage f P`: the progression with origin `f P.origin`, steps
  `f (P.origin + P.step i) - f P.origin` and the bounds of `P`.

## Main statements

* `GAP.apply_origin_add_linearCombination`: on the points of a GAP `Q`, a Freiman
  `2`-homomorphism `f` is affine. It sends `Q.origin + ∑ i, w i • Q.step i` to
  `f Q.origin + ∑ i, w i • (f (Q.origin + Q.step i) - f Q.origin)`.
* `GAP.toFinset_freimanImage` and `GAP.proper_freimanImage`: a Freiman `2`-homomorphism `f`
  defined on the points of a GAP `P` maps them onto the points of `P.freimanImage f`, which is
  proper when `P` is proper and `f` is a Freiman `2`-isomorphism.
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

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- The progression with origin `f P.origin`, steps `f (P.origin + P.step i) - f P.origin` and the
bounds of `P`. Its points are the image of the points of `P` under a Freiman `2`-homomorphism `f`
(`GAP.toFinset_freimanImage`). -/
@[expose] def freimanImage (f : H → G) (P : GAP H) : GAP G :=
  ⟨P.dim, f P.origin, fun i ↦ f (P.origin + P.step i) - f P.origin, P.bound⟩

@[simp] lemma dim_freimanImage (f : H → G) (P : GAP H) : (P.freimanImage f).dim = P.dim := rfl

variable [DecidableEq G] [DecidableEq H]

/-! ### Rigidity of a progression under a Freiman 2-homomorphism -/

omit [DecidableEq G] in
private lemma origin_add_linearCombination_mem (Q : GAP H) {w : Fin Q.dim → ℕ}
    (hw : w ≤ Q.bound) : Q.origin + Fintype.linearCombination ℕ Q.step w ∈ (Q : Finset H) := by
  rw [Fintype.linearCombination_apply]
  exact Q.eval_mem_toFinset hw

omit [DecidableEq G] in
/-- Adding the `i`-th step inside the points of a GAP `Q` changes the image under a Freiman
`2`-homomorphism `f` by `f (Q.origin + Q.step i) - f Q.origin`. -/
private lemma apply_add_step (Q : GAP H) {B : Set G} {f : H → G}
    (hf : IsAddFreimanHom 2 (Q : Set H) B f) {i : Fin Q.dim} {x : H} (hx : x ∈ (Q : Finset H))
    (hxi : x + Q.step i ∈ (Q : Finset H)) (hi : Q.origin + Q.step i ∈ (Q : Finset H)) :
    f (x + Q.step i) = f x + (f (Q.origin + Q.step i) - f Q.origin) := by
  rw [← add_sub_assoc, eq_sub_iff_add_eq]
  exact hf.add_eq_add hxi Q.origin_mem hx hi (by abel)

omit [DecidableEq G] in
/-- On the points of a GAP `Q`, a Freiman `2`-homomorphism `f` is affine: it sends
`Q.origin + ∑ i, w i • Q.step i` to
`f Q.origin + ∑ i, w i • (f (Q.origin + Q.step i) - f Q.origin)`. -/
lemma apply_origin_add_linearCombination (Q : GAP H) {B : Set G} {f : H → G}
    (hf : IsAddFreimanHom 2 (Q : Set H) B f) {w : Fin Q.dim → ℕ} (hw : w ≤ Q.bound) :
    f (Q.origin + Fintype.linearCombination ℕ Q.step w) =
      f Q.origin +
        Fintype.linearCombination ℕ (fun i ↦ f (Q.origin + Q.step i) - f Q.origin) w := by
  induction w using WellFoundedLT.induction with
  | _ w ih =>
  obtain rfl | ⟨i, hi : w i ≠ 0⟩ := (eq_or_ne w 0).imp_right Function.ne_iff.1
  · simp
  obtain ⟨u, rfl⟩ := exists_eq_add_single hi
  have hu : u ≤ Q.bound := fun j ↦ (Nat.le_add_right _ _).trans (hw j)
  have hw' := Q.origin_add_linearCombination_mem hw
  simp only [map_add, Fintype.linearCombination_apply_single, one_smul, ← add_assoc] at hw' ⊢
  rw [Q.apply_add_step hf (Q.origin_add_linearCombination_mem hu) hw' (by
    simpa using Q.origin_add_linearCombination_mem fun j ↦ (Nat.le_add_left _ _).trans (hw j)),
    ih u (Pi.lt_def.2 ⟨fun j ↦ Nat.le_add_right _ _, i, by simp⟩) hu]

/-- The image of the points of a GAP `P` under a Freiman `2`-homomorphism `f` is the set of points
of `P.freimanImage f`. -/
lemma toFinset_freimanImage {P : GAP H} {B : Set G} {f : H → G}
    (hf : IsAddFreimanHom 2 (P : Set H) B f) :
    (P.freimanImage f : Finset G) = (P : Finset H).image f := by
  rw [toFinset, toFinset, image_image]
  apply image_congr
  rintro (w : Fin P.dim → ℕ) hw
  have h := P.apply_origin_add_linearCombination hf (mem_Iic.1 hw)
  rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply] at h
  exact h.symm

omit [DecidableEq G] in
/-- A Freiman `2`-isomorphism defined on the points of a proper GAP `P` maps it onto the proper
GAP `P.freimanImage f`, which has `P.size` elements. -/
lemma proper_freimanImage {P : GAP H} (hP : P.Proper) {B : Set G} {f : H → G}
    (hf : IsAddFreimanIso 2 (P : Set H) B f) : (P.freimanImage f).Proper := by
  classical
  rw [proper_iff_card_eq_size, toFinset_freimanImage hf.isAddFreimanHom,
    card_image_of_injOn hf.bijOn.injOn, P.card_eq_size hP]
  rfl

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
    (hQB : (Q : Finset H) ⊆ (B + B) - (B + B)) :
    ∃ R : GAP G, R.Proper ∧ R.dim ≤ Q.dim ∧ #(R : Finset G) = #(Q : Finset H) ∧
      (R : Finset G) ⊆ (A + A) - (A + A) := by
  have hf := isAddFreimanIso_signedTransport hφ.invFunOn (coe_subset.2 hQB)
  refine ⟨Q.freimanImage _, GAP.proper_freimanImage hQ hf, le_rfl, ?_, ?_⟩ <;>
    rw [GAP.toFinset_freimanImage hf.isAddFreimanHom]
  · exact card_image_of_injOn hf.bijOn.injOn
  · rw [image_subset_iff]
    intro z hz
    exact signedTransport_mem hφ.invFunOn.bijOn.mapsTo (hQB hz)

end

end ChangFreimanRuzsa
