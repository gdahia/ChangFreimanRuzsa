# Chang's theorem

Lean 4 proof of Chang's theorem, the polynomial form of Freiman's theorem from Mei-Chu Chang,
[*A polynomial bound in Freiman's theorem*](https://doi.org/10.1215/S0012-7094-02-11331-3), Duke
Math. J. 113 (2002): a set with small doubling lies in a generalized arithmetic progression of
comparable size. The progression $P$ is $2$-proper in the sense that $P + P$ is proper, which is
weaker than the $2$-properness of Proposition 1.3 of Ben Green and Terence Tao,
[*Compressions, convex geometry and the Freiman–Bilu theorem*](https://arxiv.org/abs/math/0511069).
The bounds proved here are weaker than Chang's. The proof uses Chang's lemma on large spectra
from [APAP](https://github.com/YaelDillies/apap) and Minkowski's second theorem from
[Tau Ceti](https://github.com/TauCetiProject/TauCeti).

## Results

A generalized arithmetic progression (`ChangFreimanRuzsa.GAP`) in an abelian group $G$ has an
origin $a$ and a finitely supported bound $b : G \to \mathbb{N}$. Its points are
$a + \sum_v c_v v$ with $c \le b$. Its steps are the $v$ with $b_v \ne 0$, the length of the step
$v$ is $b_v + 1$, and its dimension is the number of steps. It is proper (`GAP.Proper`) if these
points are distinct. The sum $P + Q$ adds the origins and the bounds, so its points are the sums
of a point of $P$ and a point of $Q$. A progression $P$ is $2$-proper (`GAP.TwoProper`) if
$P + P$ is proper, as in Bilu's condition $F_2$ and in Tao and Vu. For steps $s_i$ and lengths
$\ell_i$, this asks the points $2a + \sum_i w_i s_i$ with $0 \le w_i \le 2\ell_i - 2$ to be
distinct. Definition 1.1 of Green and Tao with $t = 2$ asks the same for
$0 \le w_i \le 2\ell_i - 1$, which is stronger: the progression $\{0, 1\}$ in
$\mathbb{Z}/3\mathbb{Z}$ is $2$-proper here but not in their sense.

The Freiman dimension $\mathrm{dim}_\mathrm{F} X$ of a finite set $X$ is the largest
$d \le |X|$ such that $X$ is Freiman isomorphic of order $2$ to a subset of $\mathbb{Q}^d$ that
is not contained in a proper affine subspace. It is `SumOfSetsInSeveralDimensions.freimanDim`, from
[SumOfSetsInSeveralDimensions](https://github.com/gdahia/SumOfSetsInSeveralDimensions), a Lake
dependency.

**Theorem 1** (`ChangFreimanRuzsa.exists_twoProperGAP_subset_dim_le_freimanDim_card_le`). Let
$\kappa \ge 2$ and let $X$ be a finite nonempty set of integers with $|X + X| \le \kappa |X|$.
Then $X$ is contained in a $2$-proper progression $P$ with

$$\dim P \le \mathrm{dim}_\mathrm{F} X, \qquad |P| \le \exp(10^{32} \kappa^7) |X|.$$

**Theorem 2** (`ChangFreimanRuzsa.exists_twoProperGAP_zmod_subset_dim_le_freimanDim_card_le`).
Let $q$ be a prime, let $\kappa \ge 2$, and let $X \subseteq \mathbb{Z}/q\mathbb{Z}$ satisfy
$|X + X| \le \kappa |X|$, $|X| \ge 7 \cdot 10^7 \kappa^2$ and
$\exp(10^{30} \kappa^7) |X| \le q$. Then $X$ is contained in a $2$-proper progression $Q$ with

$$\dim Q \le \mathrm{dim}_\mathrm{F} X, \qquad |Q| \le \exp(10^{30} \kappa^7) |X|.$$

**Corollary** (`ChangFreimanRuzsa.exists_twoProperGAP_subset_dim_le_card_le` and
`ChangFreimanRuzsa.exists_twoProperGAP_zmod_subset_dim_le_card_le`). Under the hypotheses of
Theorems 1 and 2, the progression has dimension at most $2\kappa - 1$, since the Freiman dimension
of a nonempty set $X$ with $|X + X| \le \kappa |X|$ is at most $2\kappa - 1$
(`SumOfSetsInSeveralDimensions.freimanDim_le_two_mul_sub_one_of_card_add_le`).

Chang's theorem, as stated by Green and Tao, gives a progression with at most
$\exp(C \kappa^2 \log^3 \kappa) |X|$ points and dimension at most the Freiman dimension of $X$.
Theorems 1 and 2 have the same bound on the dimension, and a bound on the size that is linear in
$|X|$ too, with a larger exponent.

[Challenge.lean](ChangFreimanRuzsaPalomar/Challenge.lean) contains the two statements of the
corollary, under the library names with a prime and with `sorry` placeholders, together with the
definitions of `GAP`, of its points, dimension, properness and sum, and of `GAP.TwoProper`. They
are stated in terms of Mathlib, which has
no Freiman dimension, so Theorems 1 and 2 are not part of `Challenge.lean`.
[Solution.lean](ChangFreimanRuzsaPalomar/Solution.lean) proves each statement by the library
theorem. The library and the solution contain no `sorry`, and the
theorems depend on no axioms other than `propext`, `Classical.choice` and `Quot.sound`.

The library also states the theorems with named exponents, which the explicit bounds above replace:

| Theorem | Named bound | Bound for `κ ≥ 2` |
| --- | --- | --- |
| `exists_twoProperGAP_int_dim_le_freimanDim`, exponent of the size | `intFreimanDimExponent κ` | at most `10 ^ 32 * κ ^ 7` |
| `exists_twoProperGAP_zmod_dim_le_freimanDim`, exponent of the size | `freimanDimExponent κ` | at most `10 ^ 30 * κ ^ 7` |
| `exists_twoProperGAP_zmod_dim_le_freimanDim`, lower bound on `\|X\|` | `256 * bohrGAPDim κ` | at most `7 * 10 ^ 7 * κ ^ 2` |

## Files

| Files in `ChangFreimanRuzsa/` | Contents |
| --- | --- |
| `GeneralizedArithmeticProgression.lean`, `GapToolkit.lean` | Progressions, proper and `2`-proper progressions, Freiman isomorphisms |
| `RuzsaModel.lean` | Ruzsa's model lemma |
| `Fourier.lean` | Chang's lemma for subsets of `ZMod q`, Bohr sets |
| `MinkowskiSecond.lean` | Minkowski's second theorem for a weighted sum of squares |
| `BohrProgression.lean` | A proper progression inside a Bohr set |
| `FreimanRigidity.lean` | Images of progressions under Freiman isomorphisms |
| `Packing.lean` | Chang's covering argument |
| `Container.lean` | The progression containing `X`, with the exponent `containerExponent` |
| `GeometryOfNumbers.lean`, `ConvexGeometry.lean`, `IntVectorToReal.lean`, `Lattice.lean`, `BoxLatticePoints.lean` | Lattices, convex bodies and shortest lattice vectors |
| `LatticeBox/` | Covering the lattice points of a convex body by a box in a lattice basis |
| `Properization/` | Relations of a progression, saturated spans, Smith normal form quotients, short relations and the passage to a `2`-proper progression |
| `Cyclic.lean` | Chang's theorem in `ZMod q` with named exponents |
| `Integers.lean` | Chang's theorem for sets of integers with named exponents |
| `Bound.lean` | Polynomial bounds for the exponents of `Container.lean`, `Cyclic.lean` and `Integers.lean` |
| `ExplicitBounds.lean` | Theorems 1 and 2 and the corollary |
| `LatticeCoordinates.lean`, `LatticeBox/EffectiveLattice.lean` | Coordinates in a basis of the lattice of integer points of the span of a finite set of integer vectors |
| `FreimanModel.lean` | The Freiman model of a subset of a `2`-proper progression |
| `CoordinateReduction.lean` | A `2`-proper progression of dimension at most `freimanDim X` containing `X` |
| `CyclicFreimanDimension.lean` | Chang's theorem in `ZMod q` and for sets of integers with dimension at most `freimanDim X`, with named exponents |

[formalization.yaml](formalization.yaml) records the sources, the differences from them, the
scope, and the use of AI coding agents.

## Verification

`Challenge.lean` imports only Mathlib. It repeats the library definitions of `GAP`, `GAP.eval`,
`GAP.carrier`, `GAP.dim`, `GAP.Proper`, the sum of progressions and `GAP.TwoProper` and states `exists_twoProperGAP_subset_dim_le_card_le'` and
`exists_twoProperGAP_zmod_subset_dim_le_card_le'` with `sorry`. `comparator.json` names these
two theorems, `ChangFreimanRuzsaPalomar.Challenge` and `ChangFreimanRuzsaPalomar.Solution` as the
modules to compare, and `propext`, `Classical.choice` and `Quot.sound` as the permitted axioms.
The two modules sit in `ChangFreimanRuzsaPalomar/` rather than at the root, so that they do not
clash with the `Challenge` and `Solution` modules of the projects this one requires or is
required by.

## Build

The Lean, Mathlib, APAP, AddCombi, Tau Ceti and SumOfSetsInSeveralDimensions versions are pinned
in `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`.

```sh
lake exe cache get
lake build
```

The default build includes the library, challenge, and solution. The `sorry` warnings from
`Challenge.lean` are expected.

CI also runs `scripts/check-lean-sources.py`, `scripts/validate-formalization.rb` and
`scripts/verify-comparator.sh`. The last one needs Linux with `bwrap`.
