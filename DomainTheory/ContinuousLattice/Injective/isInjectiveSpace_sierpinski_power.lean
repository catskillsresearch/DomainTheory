/-ai
Every power of the Sierpiński space is injective.

Each factor is injective, and a product of injective spaces is injective.
ai-/
module

public import Mathlib.Topology.ContinuousMap.T0Sierpinski
import all Mathlib.Topology.ContinuousMap.T0Sierpinski
public import Mathlib.Topology.ContinuousMap.Basic
import all Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Sets.Opens
import all Mathlib.Topology.Sets.Opens
public import DomainTheory.ContinuousLattice.Injective.Basic
public import DomainTheory.ContinuousLattice.Injective.proposition_1_2
public import DomainTheory.ContinuousLattice.Injective.proposition_1_3

@[expose] public section


open Topology TopologicalSpace

universe w


theorem isInjectiveSpace_sierpinski_power (ι : Type w) :
    IsInjectiveSpace.{u} (ι → Prop) :=
  proposition_1_3 (fun (_ : ι) => Prop) (fun _ => proposition_1_2)
