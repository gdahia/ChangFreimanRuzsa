/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.ContinuousFunctionalCalculus

/-! # Integer vectors as real vectors

This file defines the coordinatewise inclusion `intVectorToReal` of $\mathbb{Z}^d$ into
$\mathbb{R}^d$ and proves that it is an injective additive map.
-/

@[expose] public section

namespace ChangFreimanRuzsa

noncomputable section

/-- The coordinatewise inclusion of integer vectors into real vectors. -/
def intVectorToReal {d : ℕ} (v : Fin d → ℤ) : Fin d → ℝ := fun i ↦ v i

lemma intVectorToReal_injective {d : ℕ} :
    Function.Injective (intVectorToReal (d := d)) := by
  intro a b h
  funext i
  simpa [intVectorToReal] using congr_fun h i

@[simp] lemma intVectorToReal_zero {d : ℕ} :
    intVectorToReal (0 : Fin d → ℤ) = 0 := by
  ext i
  simp [intVectorToReal]

@[simp] lemma intVectorToReal_add {d : ℕ} (a b : Fin d → ℤ) :
    intVectorToReal (a + b) = intVectorToReal a + intVectorToReal b := by
  ext i
  simp [intVectorToReal, Pi.add_apply]

end

end ChangFreimanRuzsa
