# Chang's theorem

Lean 4 proof of Chang's theorem, the polynomial form of Freiman's theorem from Mei-Chu Chang,
[*A polynomial bound in Freiman's theorem*](https://doi.org/10.1215/S0012-7094-02-11331-3), Duke
Math. J. 113 (2002): a set with small doubling lies in a generalized arithmetic progression of
comparable size. The progression is $2$-proper, as in Proposition 1.3 of Ben Green and Terence
Tao, [*Compressions, convex geometry and the Freiman–Bilu theorem*](https://arxiv.org/abs/math/0511069).
The bounds proved here are weaker than Chang's. The proof uses Chang's lemma on large spectra
from [APAP](https://github.com/YaelDillies/apap) and Minkowski's second theorem from
[Tau Ceti](https://github.com/TauCetiProject/TauCeti).

## Results

A generalized arithmetic progression (`ChangFreimanRuzsa.GAP`) of dimension $d$ in an abelian
group has an origin $a$, steps $s_0, \dots, s_{d-1}$ and lengths $\ell_0, \dots, \ell_{d-1} \ge 1$.
Its points are $a + \sum_i w_i s_i$ with $0 \le w_i < \ell_i$. It is $2$-proper
(`GAP.TwoProper`) if the points $2a + \sum_i w_i s_i$ with $0 \le w_i < 2\ell_i$ are distinct.

The Freiman dimension of a finite set $X$ is the largest $d \le |X|$ such that $X$ is Freiman
isomorphic of order $2$ to a subset of $\mathbb{Q}^d$ that is not contained in a proper affine
subspace. It is `SumOfSetsInSeveralDimensions.freimanDim`, from
[SumOfSetsInSeveralDimensions](https://github.com/gdahia/SumOfSetsInSeveralDimensions), a Lake
dependency.

**Theorem 1** (`ChangFreimanRuzsa.exists_twoProperGAP_subset_dim_le_freimanDim_card_le`). Let
$\kappa \ge 2$ and let $X$ be a finite nonempty set of integers with $|X + X| \le \kappa |X|$.
Then $X$ is contained in a $2$-proper progression $P$ with

$$\dim P \le \operatorname{freimanDim} X, \qquad |P| \le \exp(10^{32} \kappa^7) |X|.$$

**Theorem 2** (`ChangFreimanRuzsa.exists_twoProperGAP_zmod_subset_dim_le_freimanDim_card_le`).
Let $q$ be a prime, let $\kappa \ge 2$, and let $X \subseteq \mathbb{Z}/q\mathbb{Z}$ satisfy
$|X + X| \le \kappa |X|$, $|X| > \exp(2 \cdot 10^8 \kappa^3)$ and
$\exp(10^{30} \kappa^7) |X| \le q$. Then $X$ is contained in a $2$-proper progression $Q$ with

$$\dim Q \le \operatorname{freimanDim} X, \qquad |Q| \le \exp(10^{30} \kappa^7) |X|.$$

**Corollary** (`ChangFreimanRuzsa.exists_twoProperGAP_subset_dim_le_card_le` and
`ChangFreimanRuzsa.exists_twoProperGAP_zmod_subset_dim_le_card_le`). Under the hypotheses of
Theorems 1 and 2, the progression has dimension at most $2\kappa - 1$, since the Freiman dimension
of a nonempty set $X$ with $|X + X| \le \kappa |X|$ is at most $2\kappa - 1$
(`SumOfSetsInSeveralDimensions.freimanDim_le_two_mul_sub_one_of_card_add_le`).

Chang's theorem, as stated by Green and Tao, gives a progression with at most
$\exp(C \kappa^2 \log^3 \kappa) |X|$ points and dimension at most the Freiman dimension of $X$.
Theorems 1 and 2 have the same bound on the dimension, and a bound on the size that is linear in
$|X|$ too, with a larger exponent.

[Challenge.lean](Challenge.lean) contains the two statements of the corollary, under the library
names with a prime and with `sorry` placeholders, together with the definitions of `gapMap`, `GAP`
and `GAP.TwoProper`. They are stated in terms of Mathlib, which has no Freiman dimension, so
Theorems 1 and 2 are not part of `Challenge.lean`. [Solution.lean](Solution.lean) proves each
statement by the library theorem. The library and the solution contain no `sorry`, and the
theorems depend on no axioms other than `propext`, `Classical.choice` and `Quot.sound`.

The library also states the theorems with named exponents, which the explicit bounds above replace:

| Theorem | Exponent | Bound for `κ ≥ 2` |
| --- | --- | --- |
| `exists_twoProperGAP_int_dim_le_freimanDim`, size | `intFreimanDimExponent κ` | at most `10 ^ 32 * κ ^ 7` |
| `exists_twoProperGAP_zmod_dim_le_freimanDim`, size | `freimanDimExponent κ` | at most `10 ^ 30 * κ ^ 7` |
| `exists_twoProperGAP_zmod_dim_le_freimanDim`, lower bound on `\|X\|` | `containerExponent κ` | at most `2 * 10 ^ 8 * κ ^ 3` |

The progressions before the reduction of the dimension have the following exponents:

| Theorem | Exponent | Bound for `κ ≥ 2` |
| --- | --- | --- |
| `exists_twoProperGAP_of_small_sumset`, for integers, size | `intExponent κ` | at least `κ ^ 2`, at most `4 * 10 ^ 31 * κ ^ 7` |
| `exists_twoProperGAP_of_small_sumset`, for integers, dimension | `containerExponent (2 * κ)` | at most `16 * 10 ^ 8 * κ ^ 3` |
| `exists_twoProperGAP_zmod_of_small_sumset`, size | `zmodExponent κ` | at most `3 * 10 ^ 29 * κ ^ 7` |
| `exists_twoProperGAP_zmod_of_small_sumset`, dimension and lower bound on `\|X\|` | `containerExponent κ` | at most `2 * 10 ^ 8 * κ ^ 3` |
| `exists_twoProperGAP_int_of_small_sumset` | the exponents of `exists_twoProperGAP_zmod_of_small_sumset` | for integers with `exp (containerExponent κ) < \|X\|` |

## Proof

Let $X \subseteq \mathbb{Z}/q\mathbb{Z}$ with $|X + X| \le \kappa |X|$. Ruzsa's model lemma gives a
subset $X_1 \subseteq X$ with $8|X_1| \ge |X|$ and a Freiman isomorphism of order $8$ from $X_1$
onto a subset $Y$ of $\mathbb{Z}/m\mathbb{Z}$ with $m \le 8 \kappa^{16} |Y|$. By Chang's lemma the
large spectrum of $Y$ is spanned by a dissociated set $\Delta$ with $|\Delta| = O(\kappa \log \kappa)$,
and $2Y - 2Y$ contains the Bohr set of $\Delta$. Minkowski's second theorem, applied to the lattice
of the frequencies of $\Delta$, gives a proper progression $Q$ of dimension $d = |\Delta| + 1$
inside that Bohr set, with $m \le (8d)^{3d} |Q|$. The Freiman isomorphism carries it back to a
proper progression inside $2X_1 - 2X_1$. Chang's covering argument repeatedly adds to the
progression a set of $\lceil 3\kappa \rceil$ elements of $X_1$ with disjoint translates. By the
Plünnecke–Ruzsa inequality this stops after $O(d \log d)$ steps, with $X_1 \subseteq F + (S - S)$
for the current set $S$ and a set $F$ of at most $\lceil 3\kappa \rceil$ elements. The elements of
$F$ become further steps, and Ruzsa's covering lemma recovers $X$ with at most $8\kappa$ more. The
result is a progression containing $X$, not necessarily proper, of dimension at most
`containerExponent κ` $= O(\kappa^2 \log^2 \kappa)$. The covering argument holds for a finite
subset of any abelian group, so the group need not be finite.

A progression is $2$-proper when its steps satisfy no short linear relation. If there is one, the
progression is contained in a progression of smaller dimension whose size is larger by a factor
$e^{O(D^2 \log D)}$, where $D$ is the dimension: the lattice of short relations is saturated, the
box of coefficients is projected along it, and the projection is covered by a box in a basis of
the quotient lattice. Since the dimension decreases, iterating gives a $2$-proper progression, at
the cost of a factor $e^{3 (D + 2)^3 \log (D + 2)}$ (`properizationExponent`). With
$D = O(\kappa^2 \log^2 \kappa)$ this is $e^{O(\kappa^6 \log^7 \kappa)}$, which is at most
$e^{C \kappa^7}$. The saturation step needs the multiples $n a$, for $n$ up to a bound, of every
nonzero $a$ to be distinct. This holds in $\mathbb{Z}/q\mathbb{Z}$ when the prime $q$ is large
compared with the progression, and in a torsion-free group.

The dimension is reduced to the Freiman dimension as in Appendix A of Marcelo Campos, Gabriel
Dahia and João Pedro Marciano, *On the independence number of sparser random Cayley graphs*,
J. London Math. Soc. 110 (2024). Let $X$ lie in a $2$-proper progression $P$. The coefficient
vectors of the elements of $X$, translated so that one of them is the origin, span a subspace $H$
of dimension $r$. In a basis of the lattice of integer points of $H$, these vectors form a Freiman
model of $X$ of dimension $r$, so $r$ is at most the Freiman dimension of $X$. The integer points
of $H$ in the box of differences of coefficient vectors are covered by a box in that basis. This
gives a progression of dimension $r$ containing $X$, and the previous step makes it $2$-proper.

For a finite set $X$ of integers, Theorem 2 cannot be used directly: a progression of
$\mathbb{Z}/q\mathbb{Z}$ that contains the reduction of $X$ may wrap around, and then it is not
the reduction of a progression of integers that contains $X$. Instead, only the first step is
done modulo a prime $q > 16 \max_{x \in X} |x|$. It gives a proper progression inside
$2X_1 - 2X_1$ for the reduction of $X$. On $X$ the reduction modulo $q$ is a Freiman isomorphism
of order $8$, so the progression is carried back to a proper progression of integers inside
$2X_1 - 2X_1$. The covering argument, the passage to a $2$-proper progression and the reduction of
the dimension then take place in $\mathbb{Z}$. A set $X$ with at most
$\exp(\mathtt{containerExponent}\ \kappa)$ elements is first replaced by a larger set that
contains it, its sum with a long progression of large common difference. The reduction of the
dimension is applied to $X$ itself, inside the $2$-proper progression that contains the larger
set, so the dimension is at most the Freiman dimension of $X$ for every finite set of integers.

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

`APAPCompat/` contains eight modules of APAP in which the four lemmas that mention APAP's
`Submodule.finrank` are stated with `Module.finrank` of the submodule. PFR declares
`Submodule.finrank` too, so with these modules the library can be imported together with
[PFR](https://github.com/teorth/pfr). The other modules of APAP are imported from the package.

[formalization.yaml](formalization.yaml) records the sources, the differences from them, the
scope, and the use of AI coding agents.

## Verification

`Challenge.lean` imports only Mathlib. It repeats the library definitions of `gapMap`, `GAP` and
`GAP.TwoProper` and states `exists_twoProperGAP_subset_dim_le_card_le'` and
`exists_twoProperGAP_zmod_subset_dim_le_card_le'` with `sorry`. `comparator.json` names these
two theorems, `Challenge` and `Solution` as the modules to compare, and `propext`,
`Classical.choice` and `Quot.sound` as the permitted axioms.

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
