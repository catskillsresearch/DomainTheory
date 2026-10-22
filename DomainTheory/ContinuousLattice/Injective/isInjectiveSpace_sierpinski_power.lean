module

public import Mathlib.Topology.ContinuousMap.T0Sierpinski
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Sets.Opens
public import DomainTheory.ContinuousLattice.Injective.Basic
public import DomainTheory.ContinuousLattice.Injective.proposition_1_2
public import DomainTheory.ContinuousLattice.Injective.proposition_1_3

@[expose] public section


open Topology TopologicalSpace

universe w


theorem isInjectiveSpace_sierpinski_power (ι : Type w) :
    InjectiveSpace.{u} (ι → Prop) :=
  proposition_1_3 (fun (_ : ι) => Prop) (fun _ => proposition_1_2)
