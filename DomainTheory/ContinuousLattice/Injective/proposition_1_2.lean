/-ai
The Sierpiński space is injective.

This is the injectivity of the space of propositions.
ai-/
module

public import Mathlib.Topology.ContinuousMap.T0Sierpinski
import all Mathlib.Topology.ContinuousMap.T0Sierpinski
public import Mathlib.Topology.ContinuousMap.Basic
import all Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Sets.Opens
import all Mathlib.Topology.Sets.Opens
public import DomainTheory.ContinuousLattice.Injective.Basic
public import DomainTheory.ContinuousLattice.Injective.isInjectiveSpace_sierpinski

@[expose] public section


open Topology TopologicalSpace


theorem proposition_1_2 : IsInjectiveSpace.{u} Sierpinski :=
  isInjectiveSpace_sierpinski
