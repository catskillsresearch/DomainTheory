module

public import DomainTheory.ContinuousLattice.Injective.InjectiveSpace
public import Mathlib.Topology.Constructions
import DomainTheory.ContinuousLattice.Injective.IsInjectiveSpaceu2epi

@[expose] public section


open Topology TopologicalSpace

universe v w


theorem proposition_1_3 {ι : Type w} (D : ι → Type v) [∀ i, TopologicalSpace (D i)]
    (h : ∀ i, InjectiveSpace.{u} (D i)) : InjectiveSpace.{u} (∀ i, D i) :=
  InjectiveSpace.pi D h
