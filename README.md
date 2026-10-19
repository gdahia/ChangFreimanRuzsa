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

**Theorem 1** (`ChangFreimanRuzsa.exists_twoProperGAP_subset_dim_le_card_le`). Let
$\kappa \ge 2$ and let $X$ be a finite nonempty set of integers with $|X + X| \le \kappa |X|$.
Then $X$ is contained in a $2$-proper progression $P$ with

$$\dim P \le 3 \cdot 10^{14} \kappa^5, \qquad |P| \le \exp(10^{59} \kappa^{20}) |X|.$$

**Theorem 2** (`ChangFreimanRuzsa.exists_twoProperGAP_zmod_subset_dim_le_card_le`). Let $q$ be a
prime, let $\kappa \ge 2$, and let $X \subseteq \mathbb{Z}/q\mathbb{Z}$ satisfy
$|X + X| \le \kappa |X|$, $|X| > \exp(7 \cdot 10^{12} \kappa^5)$ and
$\exp(10^{53} \kappa^{20}) |X| \le q$. Then $X$ is contained in a $2$-proper progression $Q$ with

$$\dim Q \le 7 \cdot 10^{12} \kappa^5, \qquad |Q| \le \exp(10^{53} \kappa^{20}) |X|.$$

Chang's theorem, as stated by Green and Tao, gives a progression with at most
$\exp(C \kappa^2 \log^3 \kappa) |X|$ points and dimension at most the Freiman dimension of $X$.
The bounds here are linear in $|X|$ too, with a larger constant.

The Freiman dimension of a finite set $X$ is the largest $d \le |X|$ such that $X$ is Freiman
isomorphic of order $2$ to a subset of $\mathbb{Q}^d$ that is not contained in a proper affine
subspace. It is `SumOfSetsInSeveralDimensions.freimanDim`, from
[SumOfSetsInSeveralDimensions](https://github.com/gdahia/SumOfSetsInSeveralDimensions), a Lake
dependency.

**Dimension at most the Freiman dimension**
(`ChangFreimanRuzsa.exists_twoProperGAP_zmod_dim_le_freimanDim` and
`ChangFreimanRuzsa.exists_twoProperGAP_int_dim_le_freimanDim`). Under the hypotheses of
Theorem 2, with the budget `changFreimanDimExponent κ` in place of $10^{53} \kappa^{20}$, the
$2$-proper progression can be taken of dimension at most the Freiman dimension of $X$. The same
holds for a finite set $X$ of integers with $|X| > \exp(\mathtt{changContainerExponent}\ \kappa)$,
with no upper bound on $|X|$.

**Dimension at most $2\kappa - 1$**
(`ChangFreimanRuzsa.exists_twoProperGAP_zmod_dim_le_two_mul_sub_one` and
`ChangFreimanRuzsa.exists_twoProperGAP_int_dim_le_two_mul_sub_one`). Under the same hypotheses,
the progression has dimension at most $2\kappa - 1$, since the Freiman dimension of a nonempty
set $X$ with $|X + X| \le \kappa |X|$ is at most $2\kappa - 1$
(`SumOfSetsInSeveralDimensions.freimanDim_le_two_mul_sub_one_of_card_add_le`).

[Challenge.lean](Challenge.lean) contains Theorems 1 and 2 in terms of Mathlib, with the
definitions of `gapMap`, `GAP` and `GAP.TwoProper`, under the same names with a prime and with
`sorry` placeholders, and [Solution.lean](Solution.lean) proves each of them by the library
theorem. The statements with the Freiman dimension and with $2\kappa - 1$ are not part of
`Challenge.lean`. The library and the solution contain no `sorry`, and the theorems depend on no
axioms other than `propext`, `Classical.choice` and `Quot.sound`.

The library also states the theorems with named budgets, which the explicit bounds above replace:

| Theorem | Budget | Bound for `κ ≥ 2` |
| --- | --- | --- |
| `exists_twoProperGAP_of_small_sumset`, for integers, size | `changIntExponent κ` | at least `κ ^ 2`, at most `10 ^ 59 * κ ^ 20` |
| `exists_twoProperGAP_of_small_sumset`, for integers, dimension | `changContainerExponent (2 * κ)` | at most `3 * 10 ^ 14 * κ ^ 5` |
| `exists_twoProperGAP_zmod_of_small_sumset`, size | `changZModExponent κ` | at most `10 ^ 53 * κ ^ 20` |
| `exists_twoProperGAP_zmod_of_small_sumset`, dimension and lower bound on `\|X\|` | `changContainerExponent κ` | at most `7 * 10 ^ 12 * κ ^ 5` |
| `exists_twoProperGAP_zmod_dim_le_freimanDim` and `exists_twoProperGAP_int_dim_le_freimanDim`, size | `changFreimanDimExponent κ` | at most `10 ^ 53 * κ ^ 20` |
| `exists_twoProperGAP_int_of_small_sumset` | the budgets of `exists_twoProperGAP_zmod_of_small_sumset` | for integers with `exp (changContainerExponent κ) < \|X\|` |

## Proof

Let $X \subseteq \mathbb{Z}/q\mathbb{Z}$ with $|X + X| \le \kappa |X|$. Ruzsa's model lemma gives a
subset $X_1 \subseteq X$ with $8|X_1| \ge |X|$ and a Freiman isomorphism of order $8$ from $X_1$
onto a subset $Y$ of $\mathbb{Z}/m\mathbb{Z}$ with $m \le \kappa^{16} |X|$. By Chang's lemma the
large spectrum of $Y$ is spanned by a dissociated set $\Delta$ whose size is bounded in terms of
$\kappa$, and $2Y - 2Y$ contains the Bohr set of $\Delta$. Minkowski's second theorem, applied to
the lattice of the frequencies of $\Delta$, gives a proper progression of dimension $|\Delta| + 1$
inside that Bohr set. The Freiman isomorphism carries it back to a proper progression inside
$2X_1 - 2X_1$. Chang's covering argument adds elements of $X_1$ to the progression in batches of
$\lceil 3\kappa \rceil$ until it covers $X_1$, and Ruzsa's covering lemma recovers $X$. The result
is a progression containing $X$, not necessarily proper, of dimension at most
`changContainerExponent κ`. The covering argument holds for a finite subset of any abelian group:
the Plünnecke–Ruzsa inequality bounds the number of batches, so the group need not be finite.

A progression is $2$-proper when its steps satisfy no short linear relation. If there is one, the
progression is contained in a progression of smaller dimension whose size is larger by a factor
bounded in terms of the dimension: the lattice of short relations is saturated, the box of
coefficients is projected along it, and the projection is covered by a box in a basis of the
quotient lattice. Since the dimension decreases, iterating gives a $2$-proper progression. The
saturation step needs the multiples $n a$, for $n$ up to a bound, of every nonzero $a$ to be
distinct. This holds in $\mathbb{Z}/q\mathbb{Z}$ when the prime $q$ is large compared with the
progression, and in a torsion-free group.

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
$\exp(\mathtt{changContainerExponent}\ \kappa)$ elements is first replaced by its sum with a long
progression of large common difference.

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
| `Container.lean` | The progression containing `X`, with the budget `changContainerExponent` |
| `GeometryOfNumbers.lean`, `ConvexGeometry.lean`, `ConvexProgression.lean`, `Lattice.lean`, `BoxLatticePoints.lean` | Lattices, convex bodies and successive minima |
| `Reboxing/` | Covering the lattice points of a convex body by a box in a lattice basis |
| `Properization/` | Short relations and the passage to a `2`-proper progression |
| `Cyclic.lean` | Chang's theorem in `ZMod q` with budgets |
| `Integers.lean` | Chang's theorem for sets of integers with budgets |
| `Bound.lean` | Polynomial bounds for the budgets |
| `ExplicitBounds.lean` | Theorems 1 and 2 |
| `LatticeCoordinates.lean`, `Reboxing/EffectiveLattice.lean` | Coordinates in a basis of the lattice of integer points of the span of a finite set of integer vectors |
| `FreimanModel.lean` | The Freiman model of a subset of a `2`-proper progression |
| `CoordinateReduction.lean` | A `2`-proper progression of dimension at most `freimanDim X` containing `X` |
| `CyclicFreimanDimension.lean` | Chang's theorem in `ZMod q` and for sets of integers with dimension at most `freimanDim X`, and at most `2 * κ - 1` |

`APAPCompat/` contains eight modules of APAP in which the four lemmas that mention APAP's
`Submodule.finrank` are stated with `Module.finrank` of the submodule. PFR declares
`Submodule.finrank` too, so with these modules the library can be imported together with
[PFR](https://github.com/teorth/pfr). The other modules of APAP are imported from the package.

[formalization.yaml](formalization.yaml) records the sources, the differences from them, the
scope, and the use of AI coding agents.

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
