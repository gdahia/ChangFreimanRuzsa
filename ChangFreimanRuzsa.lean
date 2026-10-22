/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import ChangFreimanRuzsa.BohrProgression
public import ChangFreimanRuzsa.Bound
public import ChangFreimanRuzsa.BoxLatticePoints
public import ChangFreimanRuzsa.Container
public import ChangFreimanRuzsa.ConvexGeometry
public import ChangFreimanRuzsa.CoordinateReduction
public import ChangFreimanRuzsa.Cyclic
public import ChangFreimanRuzsa.CyclicFreimanDimension
public import ChangFreimanRuzsa.ExplicitBounds
public import ChangFreimanRuzsa.Fourier
public import ChangFreimanRuzsa.FreimanModel
public import ChangFreimanRuzsa.FreimanRigidity
public import ChangFreimanRuzsa.GapToolkit
public import ChangFreimanRuzsa.GeneralizedArithmeticProgression
public import ChangFreimanRuzsa.GeometryOfNumbers
public import ChangFreimanRuzsa.IntVectorToReal
public import ChangFreimanRuzsa.Integers
public import ChangFreimanRuzsa.Lattice
public import ChangFreimanRuzsa.LatticeBox.AdaptedBox
public import ChangFreimanRuzsa.LatticeBox.ConvexCardinality
public import ChangFreimanRuzsa.LatticeBox.EffectiveLattice
public import ChangFreimanRuzsa.LatticeBox.GaugeBox
public import ChangFreimanRuzsa.LatticeBox.GaugeInduction
public import ChangFreimanRuzsa.LatticeCoordinates
public import ChangFreimanRuzsa.MinkowskiSecond
public import ChangFreimanRuzsa.Packing
public import ChangFreimanRuzsa.Properization.ExponentialBounds
public import ChangFreimanRuzsa.Properization.Relations
public import ChangFreimanRuzsa.Properization.Reshape
public import ChangFreimanRuzsa.Properization.SaturatedSpan
public import ChangFreimanRuzsa.Properization.ShortRelationsAndIteration
public import ChangFreimanRuzsa.Properization.SmithQuotient
public import ChangFreimanRuzsa.RuzsaModel

/-!
# Chang's theorem

A set with small doubling lies in a `2`-proper generalized arithmetic progression of comparable
size. `ChangFreimanRuzsa.exists_twoProperGAP_zmod_of_small_sumset` is the statement for subsets of
`ZMod q` with `q` prime, and `ChangFreimanRuzsa.exists_twoProperGAP_of_small_sumset` the statement
for finite sets of integers. `ChangFreimanRuzsa.exists_twoProperGAP_zmod_subset_dim_le_card_le`
and `ChangFreimanRuzsa.exists_twoProperGAP_subset_dim_le_card_le` are the same statements with
explicit polynomial bounds. In
`ChangFreimanRuzsa.exists_twoProperGAP_zmod_dim_le_freimanDim` and
`ChangFreimanRuzsa.exists_twoProperGAP_int_dim_le_freimanDim` the progression has dimension at
most the Freiman dimension `SumOfSetsInSeveralDimensions.freimanDim` of the set.
-/
