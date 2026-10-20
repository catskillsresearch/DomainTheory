module

public import Mathlib.Topology.ContinuousMap.T0Sierpinski
import all Mathlib.Topology.ContinuousMap.T0Sierpinski
public import Mathlib.Topology.ContinuousMap.Basic
import all Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Sets.Opens
import all Mathlib.Topology.Sets.Opens
public import DomainTheory.ContinuousLattice.Injective.Basic
public import DomainTheory.ContinuousLattice.Injective.IsInjectiveSpaceu2epi

@[expose] public section



open Topology TopologicalSpace

universe u v w


theorem proposition_1_3 {ι : Type w} (D : ι → Type v) [∀ i, TopologicalSpace (D i)]
    (h : ∀ i, IsInjectiveSpace.{u} (D i)) : IsInjectiveSpace.{u} (∀ i, D i) :=
  IsInjectiveSpace.pi D h

