/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Basic.Real.Basic

/-! # Integer vectors as real vectors

This file defines the coordinatewise inclusion `intVectorToReal` of `ℤ ^ d` into `ℝ ^ d`, the
additive map `Int.castAddHom` applied in each coordinate, and proves that it is injective.
-/

@[expose] public section

namespace ChangFreimanRuzsa

noncomputable section

/-- The coordinatewise inclusion of integer vectors into real vectors, as an additive map. -/
def intVectorToReal {d : ℕ} : (Fin d → ℤ) →+ (Fin d → ℝ) := (Int.castAddHom ℝ).compLeft (Fin d)

@[simp] lemma intVectorToReal_apply {d : ℕ} (v : Fin d → ℤ) (i : Fin d) :
    intVectorToReal v i = v i := rfl

lemma intVectorToReal_injective {d : ℕ} :
    Function.Injective (intVectorToReal (d := d)) :=
  Int.cast_injective.comp_left

end

end ChangFreimanRuzsa
