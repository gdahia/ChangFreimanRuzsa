module

public import APAPCompat.Prereqs.Chang

/-!
# Chang's lemma on large spectra

`APAP` and `PFR` both declare `Submodule.finrank`, so a project that imports `PFR` cannot import
the modules of `APAP` that depend on its declaration. This library holds copies of those eight
modules, from <https://github.com/YaelDillies/apap> at commit `cfce977`, that do not use
`Submodule.finrank`. The four lemmas on the codimension of an intersection of kernels, in
`Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean` and
`Mathlib/Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean`, are stated with `Module.finrank`
of the submodule, and their proofs are adjusted. The other differences from upstream are import
lines. Everything else is imported from `APAP` itself.
-/
