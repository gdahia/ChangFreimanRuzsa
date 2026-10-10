# Chang's theorem

Lean 4 proof of Chang's theorem, the polynomial form of Freiman's theorem from Mei-Chu Chang,
[*A polynomial bound in Freiman's theorem*](https://doi.org/10.1215/S0012-7094-02-11331-3): a
set with small doubling lies in a generalized arithmetic progression of comparable size. The
progression is `2`-proper, as in Proposition 1.3 of Ben Green and Terence Tao,
[*Compressions, convex geometry and the Freiman–Bilu theorem*](https://arxiv.org/abs/math/0511069).
The bounds proved here are weaker than Chang's.

The proof for subsets of `ZMod q` comes from
[DenseSetsWithoutLargeSumsets](https://github.com/gdahia/DenseSetsWithoutLargeSumsets). It uses
Chang's lemma on large spectra from [APAP](https://github.com/YaelDillies/apap) and Minkowski's
second theorem from [Tau Ceti](https://github.com/TauCetiProject/TauCeti).

## Results

A generalized arithmetic progression (`ChangFreimanRuzsa.GAP`) of dimension `d` has an origin,
steps `step i` and lengths `length i > 0` for `i < d`. Its points are
`origin + ∑ i, w i • step i` with `w i < length i`. It is `2`-proper (`GAP.TwoProper`) if the
points with `w i < 2 * length i`, starting from `2 • origin`, are distinct.

**Sets of integers** (`ChangFreimanRuzsa.exists_twoProperGAP_subset_card_le`). Let `κ ≥ 2` and
let `X` be a finite nonempty set of integers with `|X + X| ≤ κ * |X|`. Then `X` is contained in
a `2`-proper progression with at most `exp (10 ^ 59 * κ ^ 20) * |X| ^ 2` points.

**Subsets of `ZMod q`**
(`ChangFreimanRuzsa.exists_twoProperGAP_zmod_subset_dim_le_card_le`). Let `q` be a prime, let
`κ ≥ 2`, and let `X ⊆ ZMod q` satisfy `|X + X| ≤ κ * |X|`, `exp (7 * 10 ^ 12 * κ ^ 5) < |X|` and
`exp (10 ^ 53 * κ ^ 20) * |X| ≤ q`. Then `X` is contained in a `2`-proper progression of
dimension at most `7 * 10 ^ 12 * κ ^ 5` with at most `exp (10 ^ 53 * κ ^ 20) * |X|` points.

[Solution.lean](Solution.lean) proves both. [Challenge.lean](Challenge.lean) contains the same
statements, with the definitions of `gapMap`, `GAP` and `GAP.TwoProper`, in terms of Mathlib and
with `sorry` placeholders. The library and the solution contain no `sorry`, and the theorems
depend on no axioms other than `propext`, `Classical.choice` and `Quot.sound`.

Chang's theorem, as stated by Green and Tao, gives a progression with at most
`exp (C * κ ^ 2 * (log κ) ^ 3) * |X|` points and dimension at most the Freiman dimension of `X`.
The bound for integers here is quadratic in `|X|`, and the dimension is not bounded.

The library states the two theorems with named budgets, which the explicit bounds above replace:

| Theorem | Budget | Bound for `κ ≥ 2` |
| --- | --- | --- |
| `exists_twoProperGAP_of_small_sumset`, for integers | `changIntExponent κ` | at least `κ ^ 2`, at most `10 ^ 59 * κ ^ 20` |
| `exists_twoProperGAP_zmod_of_small_sumset`, size | `changZModExponent κ` | at most `10 ^ 53 * κ ^ 20` |
| `exists_twoProperGAP_zmod_of_small_sumset`, dimension and lower bound on `\|X\|` | `changContainerExponent κ` | at most `7 * 10 ^ 12 * κ ^ 5` |

## Proof and files

Let `X ⊆ ZMod q` with `|X + X| ≤ κ * |X|`. Ruzsa's model lemma gives a subset `X₁` of `X` with
`8 * |X₁| ≥ |X|` and a Freiman isomorphism of order `8` from `X₁` onto a subset `Y` of a group
`ZMod m` with `m ≤ κ ^ 16 * |X|`. By Chang's lemma the large spectrum of `Y` is spanned by a
dissociated set `Δ` whose size is bounded in terms of `κ`, and `2Y - 2Y` contains the Bohr set
of `Δ`. Minkowski's second theorem, applied to the lattice of the frequencies of `Δ`, gives a
proper progression of dimension `|Δ| + 1` inside that Bohr set. The Freiman isomorphism carries
it back to a proper progression inside `2X₁ - 2X₁`. Chang's covering argument adds elements of
`X₁` to the progression in batches of `⌈3 * κ⌉` until it covers `X₁`, and Ruzsa's covering lemma
recovers `X`. The result is a progression containing `X`, not necessarily proper, of dimension at
most `changContainerExponent κ`.

A progression is `2`-proper when its steps satisfy no short linear relation. If there is one,
the progression is contained in a progression of smaller dimension whose size is larger by a
factor bounded in terms of the dimension: the lattice of short relations is saturated, the box
of coefficients is projected along it, and the projection is covered by a box in a basis of the
quotient lattice. Since the dimension decreases, iterating gives a `2`-proper progression.

For a finite set `X` of integers, `X` is first replaced by its sum with a long progression of
large common difference, so that it is large enough for the statement in `ZMod q`. A prime `q`
larger than the room that statement needs is chosen, the set is reduced modulo `q`, and the
`2`-proper progression found in `ZMod q` is lifted to the integers with `q` as an additional
step.

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
| `Cyclic.lean` | Chang's theorem in `ZMod q` |
| `Integers.lean` | Chang's theorem for sets of integers |
| `Bound.lean` | Polynomial bounds for the budgets |

The files other than `Cyclic.lean`, `Integers.lean` and `Bound.lean` are copied from
DenseSetsWithoutLargeSumsets at commit `5f4b915`, ported to Lean `v4.35.0-rc4`, and placed in
the namespace `ChangFreimanRuzsa`. Declarations that the proof does not use are removed, and
`BohrProgression.lean` takes its lattice vectors from Minkowski's second theorem instead of a
lattice point count.

`APAPCompat/` holds copies of eight modules of APAP. APAP declares `Submodule.finrank`, and so
does [PFR](https://github.com/teorth/pfr), so a project that imports PFR cannot import the
modules of APAP that depend on that declaration. The copies state the four lemmas that mention
it with `Module.finrank` of the submodule, and otherwise differ from APAP in import lines only.
The other modules of APAP are imported from the package. With this, the library can be imported
together with PFR.

[formalization.yaml](formalization.yaml) records the sources, the differences from them, the
scope, and the use of an AI coding agent.

## Build

The Lean, Mathlib, APAP, AddCombi and Tau Ceti versions are pinned in `lean-toolchain`,
`lakefile.toml` and `lake-manifest.json`.

```sh
lake exe cache get
lake build
```

The default build includes the library, challenge, and solution. The `sorry` warnings from
`Challenge.lean` are expected.

CI also runs `scripts/check-lean-sources.py`, `scripts/validate-formalization.rb` and
`scripts/verify-comparator.sh`. The last one needs Linux with `bwrap`.
