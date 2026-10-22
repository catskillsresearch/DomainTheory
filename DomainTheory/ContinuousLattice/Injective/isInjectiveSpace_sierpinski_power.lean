module

public import DomainTheory.ContinuousLattice.Injective.InjectiveSpace
public import Mathlib.Topology.Constructions
import DomainTheory.ContinuousLattice.Injective.proposition_1_2
import DomainTheory.ContinuousLattice.Injective.proposition_1_3

@[expose] public section


open Topology TopologicalSpace

universe w


theorem isInjectiveSpace_sierpinski_power (ι : Type w) :
    InjectiveSpace.{u} (ι → Prop) :=
  proposition_1_3 (fun (_ : ι) => Prop) (fun _ => proposition_1_2)
