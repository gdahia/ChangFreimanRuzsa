# Chang's theorem

Lean 4 proof of Chang's version of Freiman's theorem from [*A polynomial bound
in Freiman's theorem*](https://doi.org/10.1215/S0012-7094-02-11331-3), Duke
Math. J. 113 (2002). Her result complements Freiman's qualitative statement that a
set with small doubling lies in a generalized arithmetic progression of comparable
size by ensuring that the progression $P$ is $2$-proper in the sense that $P +
P$ is proper. The bounds proved here are weaker than Chang's. The proof uses
Chang's lemma on large spectra from [APAP](https://github.com/YaelDillies/apap)
and Minkowski's second theorem from [Tau Ceti](https://github.com/TauCetiProject/TauCeti).

## Results

**Theorem 1** (`ChangFreimanRuzsa.exists_twoProperGAP_subset_dim_le_freimanDim_card_le`). Let
$\kappa \ge 2$ and let $X$ be a finite nonempty set of integers. If $|X + X| \le \kappa |X|$,
then $X$ is contained in a $2$-proper progression $P$ with

$$\dim P \le \mathrm{dim}_\mathrm{F} X, \qquad |P| \le \exp(10^{32} \kappa^7) |X|$$

where $\mathrm{dim}_\mathrm{F} X$ is the Freiman dimension of $X$.

**Theorem 2** (`ChangFreimanRuzsa.exists_twoProperGAP_zmod_subset_dim_le_freimanDim_card_le`).
Let $q$ be a prime, let $\kappa \ge 2$, and let $X \subseteq \mathbb{Z}/q\mathbb{Z}$.
If $|X + X| \le \kappa |X|$, $|X| \ge 7 \cdot 10^7 \kappa^2$ and
$\exp(10^{30} \kappa^7) |X| \le q$, then $X$ is contained in a $2$-proper progression $Q$ with

$$\dim Q \le \mathrm{dim}_\mathrm{F} X, \qquad |Q| \le \exp(10^{30} \kappa^7) |X|.$$

**Theorem 3** (`ChangFreimanRuzsa.exists_twoProperGAP_subset_dim_le_card_le`). Under the
hypotheses of Theorem 1, $X$ is contained in a $2$-proper progression $P$ with

$$\dim P \le 2\kappa - 1, \qquad |P| \le \exp(10^{32} \kappa^7) |X|.$$

**Theorem 4** (`ChangFreimanRuzsa.exists_twoProperGAP_zmod_subset_dim_le_card_le`). Under the
hypotheses of Theorem 2, $X$ is contained in a $2$-proper progression $Q$ with

$$\dim Q \le 2\kappa - 1, \qquad |Q| \le \exp(10^{30} \kappa^7) |X|.$$

**Theorem 5** (`ChangFreimanRuzsa.exists_twoProperGAP_subset_dim_le_floor_card_le`). Let
$\kappa \ge 2$, let $\varepsilon$ be a real number and let $X$ be a finite set of integers. If
$|X + X| \le \kappa |X|$ and $\kappa (2\kappa - 1) \le \varepsilon |X|$, then $X$ is contained in
a $2$-proper progression $P$ with

$$\dim P \le \lfloor \kappa - 1 + \varepsilon \rfloor, \qquad |P| \le \exp(10^{32} \kappa^7) |X|.$$

**Theorem 6** (`ChangFreimanRuzsa.exists_twoProperGAP_zmod_subset_dim_le_floor_card_le`). Under
the hypotheses of Theorem 2, if moreover $\kappa (2\kappa - 1) \le \varepsilon |X|$, then $X$ is
contained in a $2$-proper progression $Q$ with

$$\dim Q \le \lfloor \kappa - 1 + \varepsilon \rfloor, \qquad |Q| \le \exp(10^{30} \kappa^7) |X|.$$

Theorems 3 to 6 follow from Theorems 1 and 2, since the Freiman dimension of a nonempty set $X$
with $|X + X| \le \kappa |X|$ is at most $2\kappa - 1$
(`SumOfSetsInSeveralDimensions.freimanDim_le_two_mul_sub_one_of_card_add_le`) and at most
$\kappa - 1 + \kappa (2\kappa - 1) / |X|$
(`SumOfSetsInSeveralDimensions.freimanDim_le_sub_one_add_mul_div_card_of_card_add_le`).

Chang's theorem, as stated by Green and Tao, gives a progression with at most
$\exp(C \kappa^2 \log^3 \kappa) |X|$ points and dimension at most the Freiman dimension of $X$,
hence at most $\lfloor \kappa - 1 + \varepsilon \rfloor$ when $|X| \ge C \kappa^2 / \varepsilon$.
Theorems 1, 2, 5 and 6 have the same bounds on the dimension, and a bound on the size that is
linear in $|X|$ too, with a larger exponent.

The first step of the proof is the Bogolyubov–Ruzsa lemma, a large proper progression inside
$2X - 2X$.

**Theorem 7** (`ChangFreimanRuzsa.exists_proper_gap_subset_nsmul_sub_nsmul_dim_le_card_le`). Let
$\kappa \ge 2$ and let $X$ be a finite set of integers. If $|X + X| \le \kappa |X|$ and
$|X| \ge 7 \cdot 10^7 \kappa^2$, then $2X - 2X$ contains a proper progression $Q$ with

$$\dim Q \le 3 \cdot 10^5 \kappa^2, \qquad |X| \le \exp(2 \cdot 10^7 \kappa^2) |Q|.$$

**Theorem 8** (`ChangFreimanRuzsa.exists_proper_gap_zmod_subset_nsmul_sub_nsmul_dim_le_card_le`).
The same holds for $X \subseteq \mathbb{Z}/q\mathbb{Z}$ with $q$ prime.

[Challenge.lean](ChangFreimanRuzsaPalomar/Challenge.lean) contains Theorems 3 to 8, under the
library names with a prime and with `sorry` placeholders, together with the definitions of `GAP`
and of its points, dimension, properness and sum. A progression `P` is `2`-proper when
`(P + P).Proper`. The statements are in terms of Mathlib, which has no Freiman dimension, so
Theorems 1 and 2 are not part of `Challenge.lean`.
[Solution.lean](ChangFreimanRuzsaPalomar/Solution.lean) proves each statement by the library
theorem. The library and the solution contain no `sorry`, and the theorems depend on no axioms
other than `propext`, `Classical.choice` and `Quot.sound`.

The library also states the theorems with named exponents, which the explicit bounds above replace:

| Theorem | Named bound | Bound for `κ ≥ 2` |
| --- | --- | --- |
| `exists_twoProperGAP_int_dim_le_freimanDim`, exponent of the size | `intFreimanDimExponent κ` | at most `10 ^ 32 * κ ^ 7` |
| `exists_twoProperGAP_zmod_dim_le_freimanDim`, exponent of the size | `freimanDimExponent κ` | at most `10 ^ 30 * κ ^ 7` |
| `exists_twoProperGAP_zmod_dim_le_freimanDim`, lower bound on `\|X\|` | `256 * bohrGAPDim κ` | at most `7 * 10 ^ 7 * κ ^ 2` |
| `exists_proper_gap_int_subset_add_sub_add_card_le`, `exists_proper_gap_zmod_subset_add_sub_add_card_le`, dimension | `bohrGAPDim κ` | at most `3 * 10 ^ 5 * κ ^ 2` |
| `exists_proper_gap_int_subset_add_sub_add_card_le`, `exists_proper_gap_zmod_subset_add_sub_add_card_le`, loss in the size | `8 * bohrLoss (bohrGAPDim κ)` | at most `exp (2 * 10 ^ 7 * κ ^ 2)` |

## Files

| Files in `ChangFreimanRuzsa/` | Contents |
| --- | --- |
| `GAP/Basic.lean`, `GAP/Coeff.lean` | Progressions, proper and `2`-proper progressions, coefficients and the Freiman isomorphism onto the coefficient box |
| `GAP/Relations.lean`, `GAP/ScaleLengths.lean`, `GAP/Symmetric.lean`, `GAP/Constructions.lean` | Relations among the steps, enlarged lengths, symmetric progressions, progressions containing subset sums and differences |
| `GAP/FreimanHom.lean` | Images of progressions under Freiman isomorphisms |
| `GeometryOfNumbers/Box.lean`, `GeometryOfNumbers/RealBox.lean` | Integer and real boxes, the packing bound, short lattice vectors |
| `GeometryOfNumbers/IntegerLattice.lean`, `GeometryOfNumbers/SaturatedSpan.lean`, `GeometryOfNumbers/LatticeCoordinates.lean` | Integer lattices in subspaces, saturated spans, coordinates in a basis of the lattice of integer points of a span |
| `GeometryOfNumbers/Gauge.lean`, `GeometryOfNumbers/ConvexDilate.lean`, `GeometryOfNumbers/GaugeBox.lean`, `GeometryOfNumbers/GaugeInduction.lean` | Shortest lattice vectors for a convex body, and a proper progression covering its lattice points |
| `GeometryOfNumbers/MinkowskiSecond.lean` | Minkowski's second theorem for a weighted sum of squares |
| `BogolyubovRuzsa/` | Ruzsa's model lemma, Chang's lemma and Bohr sets, a proper progression in a Bohr set, and the Bogolyubov–Ruzsa lemma in `ZMod q` |
| `Covering/` | Chang's packing argument and the progression containing `X`, with the exponent `containerExponent` |
| `Properization/` | Smith normal form quotients, short relations and the passage to a `2`-proper progression |
| `FreimanDimension/` | The Freiman model of a subset of a `2`-proper progression, and a `2`-proper progression of dimension at most `freimanDim X` containing `X` |
| `ZMod.lean` | Chang's theorem in `ZMod q` with named exponents |
| `Int.lean` | Chang's theorem for sets of integers with named exponents |
| `FreimanDim.lean` | Chang's theorem in `ZMod q` and for sets of integers with dimension at most `freimanDim X`, with named exponents |
| `ExponentBounds.lean` | Polynomial bounds for the exponents of `Covering/Container.lean`, `ZMod.lean` and `Int.lean` |
| `Explicit.lean` | Theorems 1 to 8 |

[formalization.yaml](formalization.yaml) records the sources, the differences from them, the
scope, and the use of AI coding agents.

## Verification

`Challenge.lean` imports only the Mathlib modules `Mathlib.Analysis.Complex.Exponential`,
`Mathlib.Data.Finsupp.Interval` and `Mathlib.Data.Nat.Prime.Defs`. It repeats the library
definitions of `GAP`, `GAP.eval`, `GAP.toFinset`, `GAP.dim`, `GAP.Proper` and the sum of
progressions, and states `exists_proper_gap_subset_nsmul_sub_nsmul_dim_le_card_le'`,
`exists_proper_gap_zmod_subset_nsmul_sub_nsmul_dim_le_card_le'`,
`exists_twoProperGAP_subset_dim_le_card_le'`,
`exists_twoProperGAP_zmod_subset_dim_le_card_le'`,
`exists_twoProperGAP_subset_dim_le_floor_card_le'` and
`exists_twoProperGAP_zmod_subset_dim_le_floor_card_le'` with `sorry`. `comparator.json` names
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
