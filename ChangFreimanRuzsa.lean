/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.BogolyubovRuzsa.BohrSet
public import ChangFreimanRuzsa.BogolyubovRuzsa.Fourier
public import ChangFreimanRuzsa.BogolyubovRuzsa.RuzsaModel
public import ChangFreimanRuzsa.BogolyubovRuzsa.ZMod
public import ChangFreimanRuzsa.Covering.Container
public import ChangFreimanRuzsa.Covering.Packing
public import ChangFreimanRuzsa.Explicit
public import ChangFreimanRuzsa.ExponentBounds
public import ChangFreimanRuzsa.FreimanDim
public import ChangFreimanRuzsa.FreimanDimension.CoordinateReduction
public import ChangFreimanRuzsa.FreimanDimension.Model
public import ChangFreimanRuzsa.GAP.Basic
public import ChangFreimanRuzsa.GAP.Coeff
public import ChangFreimanRuzsa.GAP.Constructions
public import ChangFreimanRuzsa.GAP.FreimanHom
public import ChangFreimanRuzsa.GAP.Relations
public import ChangFreimanRuzsa.GAP.ScaleLengths
public import ChangFreimanRuzsa.GAP.Symmetric
public import ChangFreimanRuzsa.GeometryOfNumbers.Box
public import ChangFreimanRuzsa.GeometryOfNumbers.ConvexDilate
public import ChangFreimanRuzsa.GeometryOfNumbers.Gauge
public import ChangFreimanRuzsa.GeometryOfNumbers.GaugeBox
public import ChangFreimanRuzsa.GeometryOfNumbers.GaugeInduction
public import ChangFreimanRuzsa.GeometryOfNumbers.IntegerLattice
public import ChangFreimanRuzsa.GeometryOfNumbers.LatticeCoordinates
public import ChangFreimanRuzsa.GeometryOfNumbers.MinkowskiSecond
public import ChangFreimanRuzsa.GeometryOfNumbers.RealBox
public import ChangFreimanRuzsa.GeometryOfNumbers.SaturatedSpan
public import ChangFreimanRuzsa.Int
public import ChangFreimanRuzsa.Properization.ExponentialBounds
public import ChangFreimanRuzsa.Properization.Iteration
public import ChangFreimanRuzsa.Properization.ShortRelations
public import ChangFreimanRuzsa.Properization.SmithQuotient
public import ChangFreimanRuzsa.ZMod

/-!
# Chang's theorem

For every `2 ≤ t`, a set with small doubling lies in a `t`-proper generalized arithmetic progression
of comparable size. `ChangFreimanRuzsa.exists_tProperGAP_zmod_of_small_sumset` is the statement for
subsets of `ZMod q` with `q` prime, and `ChangFreimanRuzsa.exists_tProperGAP_of_small_sumset` the
statement for finite sets of integers.
`ChangFreimanRuzsa.exists_tProperGAP_zmod_subset_dim_le_card_le` and
`ChangFreimanRuzsa.exists_tProperGAP_subset_dim_le_card_le` are the same statements with explicit
bounds. In `ChangFreimanRuzsa.exists_tProperGAP_zmod_dim_le_freimanDim` and
`ChangFreimanRuzsa.exists_tProperGAP_int_dim_le_freimanDim` the progression has dimension at most
the Freiman dimension `SumOfSetsInSeveralDimensions.freimanDim` of the set.
-/
