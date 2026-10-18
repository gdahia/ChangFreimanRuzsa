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
public import ChangFreimanRuzsa.ConvexProgression
public import ChangFreimanRuzsa.CoordinateReduction
public import ChangFreimanRuzsa.Cyclic
public import ChangFreimanRuzsa.CyclicFreimanDimension
public import ChangFreimanRuzsa.Fourier
public import ChangFreimanRuzsa.FreimanModel
public import ChangFreimanRuzsa.FreimanRigidity
public import ChangFreimanRuzsa.GapToolkit
public import ChangFreimanRuzsa.GeneralizedArithmeticProgression
public import ChangFreimanRuzsa.GeometryOfNumbers
public import ChangFreimanRuzsa.Integers
public import ChangFreimanRuzsa.Lattice
public import ChangFreimanRuzsa.LatticeCoordinates
public import ChangFreimanRuzsa.MinkowskiSecond
public import ChangFreimanRuzsa.Packing
public import ChangFreimanRuzsa.Properization.AlgebraAndGAPBasics
public import ChangFreimanRuzsa.Properization.ShortRelationsAndIteration
public import ChangFreimanRuzsa.Reboxing.AdaptedBox
public import ChangFreimanRuzsa.Reboxing.ConvexCardinality
public import ChangFreimanRuzsa.Reboxing.EffectiveLattice
public import ChangFreimanRuzsa.Reboxing.GaugeBox
public import ChangFreimanRuzsa.Reboxing.GaugeInduction
public import ChangFreimanRuzsa.RuzsaModel

/-!
# Chang's theorem

A set with small doubling lies in a `2`-proper generalized arithmetic progression of comparable
size. `ChangFreimanRuzsa.exists_twoProperGAP_zmod_of_small_sumset` is the statement for subsets of
`ZMod q` with `q` prime, and `ChangFreimanRuzsa.exists_twoProperGAP_of_small_sumset` the statement
for finite sets of integers. In
`ChangFreimanRuzsa.exists_twoProperGAP_zmod_dim_le_freimanDim` and
`ChangFreimanRuzsa.exists_twoProperGAP_int_dim_le_freimanDim` the progression has dimension at
most the Freiman dimension `SumOfSetsInSeveralDimensions.freimanDim` of the set.
-/
