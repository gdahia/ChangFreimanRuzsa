module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

open scoped Finset

variable {K V ι : Type*}
    [DivisionRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {s : Finset ι} {f : ι → V →ₗ[K] K}

namespace Module

lemma codim_iInf_ker_le_fintypeCard [Fintype ι] :
    finrank K V - finrank K ↥(⨅ i, (f i).ker) ≤ Fintype.card ι := by
  let F : V →ₗ[K] (ι → K) := {
    toFun x i := f i x
    map_add' x y := by ext i; simp
    map_smul' c x := by ext i; simp
  }
  have hker : F.ker = ⨅ i, (f i).ker := by ext x; simp [F, funext_iff]
  grw [← hker, ← F.finrank_range_add_finrank_ker, Submodule.finrank_le]
  simp

lemma codim_biInf_ker_le_finsetCard : finrank K V - finrank K ↥(⨅ i ∈ s, (f i).ker) ≤ #s := by
  rw [iInf_subtype']
  simpa using codim_iInf_ker_le_fintypeCard (ι := s) (f := fun i ↦ f i)

end Module
