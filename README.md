# Chang's theorem

Lean 4 proof of Chang's version of Freiman's theorem from [*A polynomial bound
in Freiman's theorem*](https://doi.org/10.1215/S0012-7094-02-11331-3), Duke
Math. J. 113 (2002). Her result complements Freiman's qualitative statement that a
set with small doubling lies in a generalized arithmetic progression of comparable
size by ensuring that the progression $P$ is $t$-proper in the sense that $t P$
is proper. The bound on the size proved here has the form
$\exp(C \kappa^2 (1 + \log \kappa)^3 + 2 \kappa \log t)$ of Chang's bound, with an explicit
constant $C$. The proof uses Chang's lemma on large spectra from
[APAP](https://github.com/YaelDillies/apap), and Minkowski's second theorem and the volume of
cross-polytopes from [Tau Ceti](https://github.com/TauCetiProject/TauCeti). The passage to a
$t$-proper progression follows the convex-body argument of Bilu, in the form of Green's notes
[*Progressions and convex geometry*](https://people.maths.ox.ac.uk/greenbj/papers/convexnotes.pdf).

## Results

**Theorem 1** (`ChangFreimanRuzsa.exists_tProperGAP_subset_dim_le_freimanDim_card_le`). Let
$t \ge 2$ be an integer, let $\kappa \ge 2$ and let $X$ be a finite nonempty set of integers. If
$\left\lvert X + X\right\rvert \le \kappa \left\lvert X\right\rvert$, then $X$ is contained in a
$t$-proper progression $P$ with

$$\dim P \le \mathrm{dim}\_\mathrm{F} X, \qquad \left\lvert P\right\rvert \le
\exp(2 \cdot 10^{11} \kappa^2 (1 + \log \kappa)^3 + 2 \kappa \log t) \left\lvert X\right\rvert$$

where $\mathrm{dim}\_\mathrm{F} X$ is the Freiman dimension of $X$.

**Theorem 2** (`ChangFreimanRuzsa.exists_tProperGAP_zmod_subset_dim_le_freimanDim_card_le`). Let $q$
be a prime, let $t \ge 2$ be an integer, let $\kappa \ge 2$, and let
$X \subseteq \mathbb{Z}/q\mathbb{Z}$. If
$\left\lvert X + X\right\rvert \le \kappa \left\lvert X\right\rvert$,
$\left\lvert X\right\rvert \ge 7 \cdot 10^7 \kappa^2$ and
$\exp(10^{10} \kappa^2 (1 + \log \kappa)^3 + 2 \kappa \log t) \left\lvert X\right\rvert \le q$,
then $X$ is contained in a $t$-proper progression $Q$ with

$$\dim Q \le \mathrm{dim}\_\mathrm{F} X, \qquad \left\lvert Q\right\rvert \le
\exp(10^{10} \kappa^2 (1 + \log \kappa)^3 + 2 \kappa \log t) \left\lvert X\right\rvert.$$

**Theorem 3** (`ChangFreimanRuzsa.exists_tProperGAP_subset_dim_le_card_le`). Under the
hypotheses of Theorem 1, $X$ is contained in a $t$-proper progression $P$ with

$$\dim P \le 2\kappa - 1, \qquad \left\lvert P\right\rvert \le
\exp(2 \cdot 10^{11} \kappa^2 (1 + \log \kappa)^3 + 2 \kappa \log t) \left\lvert X\right\rvert.$$

**Theorem 4** (`ChangFreimanRuzsa.exists_tProperGAP_zmod_subset_dim_le_card_le`). Under the
hypotheses of Theorem 2, $X$ is contained in a $t$-proper progression $Q$ with

$$\dim Q \le 2\kappa - 1, \qquad \left\lvert Q\right\rvert \le
\exp(10^{10} \kappa^2 (1 + \log \kappa)^3 + 2 \kappa \log t) \left\lvert X\right\rvert.$$

**Theorem 5** (`ChangFreimanRuzsa.exists_tProperGAP_subset_dim_le_floor_card_le`). Let $t \ge 2$ be
an integer, let $\kappa \ge 2$, let $\varepsilon$ be a real number and let $X$ be a finite set of
integers. If $\left\lvert X + X\right\rvert \le \kappa \left\lvert X\right\rvert$ and
$\kappa (2\kappa - 1) \le \varepsilon \left\lvert X\right\rvert$, then $X$ is contained in a
$t$-proper progression $P$ with

$$\dim P \le \lfloor \kappa - 1 + \varepsilon \rfloor, \qquad \left\lvert P\right\rvert \le
\exp(2 \cdot 10^{11} \kappa^2 (1 + \log \kappa)^3 + 2 \kappa \log t) \left\lvert X\right\rvert.$$

**Theorem 6** (`ChangFreimanRuzsa.exists_tProperGAP_zmod_subset_dim_le_floor_card_le`). Under the
hypotheses of Theorem 2, if moreover
$\kappa (2\kappa - 1) \le \varepsilon \left\lvert X\right\rvert$, then $X$ is contained in a
$t$-proper progression $Q$ with

$$\dim Q \le \lfloor \kappa - 1 + \varepsilon \rfloor, \qquad \left\lvert Q\right\rvert \le
\exp(10^{10} \kappa^2 (1 + \log \kappa)^3 + 2 \kappa \log t) \left\lvert X\right\rvert.$$

Theorems 3 to 6 follow from Theorems 1 and 2, since the Freiman dimension of a nonempty set $X$
with $\left\lvert X + X\right\rvert \le \kappa \left\lvert X\right\rvert$ is at most $2\kappa - 1$
(`SumOfSetsInSeveralDimensions.freimanDim_le_two_mul_sub_one_of_card_add_le`) and at most
$\kappa - 1 + \kappa (2\kappa - 1) / \left\lvert X\right\rvert$
(`SumOfSetsInSeveralDimensions.freimanDim_le_sub_one_add_mul_div_card_of_card_add_le`).

Chang's theorem, as stated by Green and Tao, gives a progression with at most
$t^{K} \exp(C \kappa^2 \log^3 \kappa) \left\lvert X\right\rvert$ points and dimension at most the
Freiman dimension of $X$, hence at most $\lfloor \kappa - 1 + \varepsilon \rfloor$ when
$\left\lvert X\right\rvert \ge C \kappa^2 / \varepsilon$. Theorems 1, 2, 5 and 6 have the same
bounds on the dimension and a bound on the size of the same form.

The first step of the proof is the Bogolyubov–Ruzsa lemma, a large proper progression inside
$2X - 2X$.

**Theorem 7** (`ChangFreimanRuzsa.exists_proper_gap_subset_nsmul_sub_nsmul_dim_le_card_le`). Let
$\kappa \ge 2$ and let $X$ be a finite set of integers. If
$\left\lvert X + X\right\rvert \le \kappa \left\lvert X\right\rvert$ and
$\left\lvert X\right\rvert \ge 7 \cdot 10^7 \kappa^2$, then $2X - 2X$ contains a proper progression
$Q$ with

$$\dim Q \le 3 \cdot 10^5 \kappa^2, \qquad \left\lvert X\right\rvert \le
\exp(2 \cdot 10^7 \kappa^2) \left\lvert Q\right\rvert.$$

**Theorem 8** (`ChangFreimanRuzsa.exists_proper_gap_zmod_subset_nsmul_sub_nsmul_dim_le_card_le`).
The same holds for $X \subseteq \mathbb{Z}/q\mathbb{Z}$ with $q$ prime.

[Challenge.lean](ChangFreimanRuzsaPalomar/Challenge.lean) contains Theorems 3 to 8, under the
library names with a prime and with `sorry` placeholders, together with the definitions of `GAP`
and of its points, dimension, properness and multiples. A progression `P` is `t`-proper when
`(t • P).Proper`. The statements are in terms of Mathlib, which has no Freiman dimension, so
Theorems 1 and 2 are not part of `Challenge.lean`.
[Solution.lean](ChangFreimanRuzsaPalomar/Solution.lean) proves each statement by the library
theorem. The library and the solution contain no `sorry`, and the theorems depend on no axioms
other than `propext`, `Classical.choice` and `Quot.sound`.

The library also states the theorems with named exponents, which the explicit bounds above replace:

| Theorem | Named bound | Bound for `κ ≥ 2` |
| --- | --- | --- |
| `exists_tProperGAP_int_dim_le_freimanDim`, exponent of the size | `intFreimanDimExponent κ + tProperExponent t (freimanDim X)` | at most `2 * 10 ^ 11 * κ ^ 2 * (1 + log κ) ^ 3 + 2 * κ * log t` |
| `exists_tProperGAP_zmod_dim_le_freimanDim`, exponent of the size | `freimanDimExponent κ + tProperExponent t (freimanDim X)` | at most `10 ^ 10 * κ ^ 2 * (1 + log κ) ^ 3 + 2 * κ * log t` |
| `exists_tProperGAP_zmod_dim_le_freimanDim`, lower bound on `\|X\|` | `256 * bohrGAPDim κ` | at most `7 * 10 ^ 7 * κ ^ 2` |
| `exists_proper_gap_int_subset_add_sub_add_card_le`, `exists_proper_gap_zmod_subset_add_sub_add_card_le`, dimension | `bohrGAPDim κ` | at most `3 * 10 ^ 5 * κ ^ 2` |
| `exists_proper_gap_int_subset_add_sub_add_card_le`, `exists_proper_gap_zmod_subset_add_sub_add_card_le`, loss in the size | `8 * bohrLoss (bohrGAPDim κ)` | at most `exp (2 * 10 ^ 7 * κ ^ 2)` |

## Files

| Files in `ChangFreimanRuzsa/` | Contents |
| --- | --- |
| `GAP/Basic.lean` | Progressions, proper and `t`-proper progressions |
| `GAP/Relations.lean`, `GAP/Symmetric.lean`, `GAP/Constructions.lean` | Relations among the steps and `t`-properness in terms of them, symmetric progressions, progressions containing subset sums and differences |
| `GAP/FreimanHom.lean` | Images of progressions under Freiman isomorphisms |
| `GeometryOfNumbers/IntegerLattice.lean`, `GeometryOfNumbers/LatticeCoordinates.lean` | Integer lattices in subspaces, saturated spans, coordinates in a basis of the lattice of integer points of a span |
| `GeometryOfNumbers/LatticePointCount.lean`, `GeometryOfNumbers/SymmetricBody.lean` | Integer points and volume, the theorem of van der Corput, symmetric convex bodies whose integer points span |
| `GeometryOfNumbers/ProjectionVolume.lean`, `GeometryOfNumbers/RealBox.lean` | The volume of a projection of a symmetric convex body, real boxes |
| `GeometryOfNumbers/MinkowskiSecond.lean` | Minkowski's second theorem for a weighted sum of squares |
| `BogolyubovRuzsa/` | Ruzsa's model lemma, Chang's lemma and Bohr sets, a proper progression in a Bohr set, and the Bogolyubov–Ruzsa lemma in `ZMod q` |
| `Covering/` | Chang's packing argument and the progression containing `X`, with the exponent `containerExponent` |
| `FreimanDimension/` | The Freiman model of a set of integer points, and the central section of a symmetric body by the span of the model |
| `Properization/` | Quotients of a symmetric body by short relations, a `t`-proper progression from a symmetric body, and the passage from a progression to a `t`-proper progression of dimension at most `freimanDim X` |
| `ZMod.lean` | Chang's theorem in `ZMod q` with dimension at most `freimanDim X` and named exponents |
| `Int.lean` | Chang's theorem for sets of integers with dimension at most `freimanDim X` and named exponents |
| `ExponentBounds.lean` | Bounds for the exponents of `Covering/Container.lean`, `Properization/ProperProgression.lean`, `ZMod.lean` and `Int.lean` |
| `Explicit.lean` | Theorems 1 to 8 |

[formalization.yaml](formalization.yaml) records the sources, the differences from them, the
scope, and the use of AI coding agents.

## Verification

`Challenge.lean` imports only the Mathlib modules `Mathlib.Analysis.SpecialFunctions.Log.Basic`,
`Mathlib.Data.Finsupp.Interval` and `Mathlib.Data.Nat.Prime.Defs`. It repeats the library
definitions of `GAP`, `GAP.eval`, `GAP.toFinset`, `GAP.dim`, `GAP.Proper` and the multiple of a
progression, and states `exists_proper_gap_subset_nsmul_sub_nsmul_dim_le_card_le'`,
`exists_proper_gap_zmod_subset_nsmul_sub_nsmul_dim_le_card_le'`,
`exists_tProperGAP_subset_dim_le_card_le'`,
`exists_tProperGAP_zmod_subset_dim_le_card_le'`,
`exists_tProperGAP_subset_dim_le_floor_card_le'` and
`exists_tProperGAP_zmod_subset_dim_le_floor_card_le'` with `sorry`. `comparator.json` names
these six theorems, `ChangFreimanRuzsaPalomar.Challenge` and `ChangFreimanRuzsaPalomar.Solution` as the
modules to compare, and `propext`, `Classical.choice` and `Quot.sound` as the permitted axioms.
The two modules sit in `ChangFreimanRuzsaPalomar/` rather than at the root, so that they do not
clash with the `Challenge` and `Solution` modules of the projects this one requires or is
required by.

## Build

The Lean, Mathlib, APAP, Tau Ceti and SumOfSetsInSeveralDimensions versions are pinned
in `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`.

```sh
lake exe cache get
lake build
```

The default build includes the library, challenge, and solution. The `sorry` warnings from
`Challenge.lean` are expected.

CI also runs `scripts/check-lean-sources.py`, `scripts/validate-formalization.rb` and
`scripts/verify-comparator.sh`. The last one needs Linux with `bwrap`.
