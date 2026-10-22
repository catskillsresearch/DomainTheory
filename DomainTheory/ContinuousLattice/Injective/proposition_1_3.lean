/-ai
A product of injective spaces is injective.

This is the preservation of injectivity by products.
ai-/
module

public import Mathlib.Topology.ContinuousMap.T0Sierpinski
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Sets.Opens
public import DomainTheory.ContinuousLattice.Injective.Basic
public import DomainTheory.ContinuousLattice.Injective.IsInjectiveSpaceu2epi

@[expose] public section


open Topology TopologicalSpace

universe v w


theorem proposition_1_3 {ι : Type w} (D : ι → Type v) [∀ i, TopologicalSpace (D i)]
    (h : ∀ i, InjectiveSpace.{u} (D i)) : InjectiveSpace.{u} (∀ i, D i) :=
  InjectiveSpace.pi D h
