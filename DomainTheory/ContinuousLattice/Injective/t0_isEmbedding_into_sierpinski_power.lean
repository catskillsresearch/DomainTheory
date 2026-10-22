module

public import Mathlib.Topology.ContinuousMap.T0Sierpinski
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Sets.Opens
public import DomainTheory.ContinuousLattice.Injective.Basic
public import DomainTheory.ContinuousLattice.Injective.proposition_1_5

@[expose] public section


open Topology TopologicalSpace

universe u


theorem t0_isEmbedding_into_sierpinski_power (X : Type u) [TopologicalSpace X] [T0Space X] :
    IsEmbedding (productOfMemOpens X) :=
  (proposition_1_5 X).2
